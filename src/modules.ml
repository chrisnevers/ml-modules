exception ModuleException of string
let error msg = raise (ModuleException msg)

(*
  Clashing identifiers could be solved with renaming (α-conversion).
  However, users would not be able to access module components by
  name. To work around this, store identifiers as a structure
  along with a stamp of their binding location. This method preserves
  the identifier's name and distinctness.
*)
module Ident = struct

  type t = {
    name: string;
    stamp: int;
  }

  let cur_stamp = ref 0

  let create s =
    incr cur_stamp;
    { name = s; stamp = !cur_stamp }

  let name id = id.name

  let equal id1 id2 = id1.stamp = id2.stamp

  type 'a tbl = (t * 'a) list

  let empty_tbl = []

  let add id data tbl = (id, data) :: tbl

  let rec find id1 tbl =
    match tbl with
    | [] -> raise Not_found
    | (id2, data) :: tl -> if equal id1 id2 then data else find id1 tl

end

(*
  Users may reference types, values, and modules directly or
  through modules. E.G. 'x' or 'M.x'
*)
type path =
  | PIdent of Ident.t
  | PDot of path * string

let rec path_equal p1 p2 =
  match p1, p2 with
  | PIdent id1, PIdent id2 -> Ident.equal id1 id2
  | PDot(r1, field1), PDot(r2, field2) ->
    path_equal r1 r2 && field1 = field2
  | _, _ -> false

(*
  To typecheck modules, identifiers need to be substituted with paths.
*)
module Subst = struct

  type t = path Ident.tbl

  let identity = Ident.empty_tbl

  let add = Ident.add

  let rec path p sub =
    match p with
    | PIdent id -> (try
      Ident.find id sub with Not_found -> p)
    | PDot(root, field) -> PDot(path root sub, field)

end

(*
  term - Ast for definitions of value names.
    E.G. Value expression in a functional language, or
    variable declaration in procedural language.
  val_type: type expressions for terms
  def_type: type expressions that can be bound to a type name.

  ML has type schemes for val_type and type constructors
  (type expressions possibly parameterized by other types) for def_type.
*)
module type CoreSyntax = sig
  type term
  type val_type
  type def_type
  type kind
  val subst_valtype: val_type -> Subst.t -> val_type
  val subst_deftype: def_type -> Subst.t -> def_type
  val subst_kind: kind -> Subst.t -> kind
end

module type ModuleSyntax = sig

  (* The core syntax of language *)
  module Core : CoreSyntax

  (*
    Abstract or manifest
    A type identifier is 'manifest' if its implementation is shown
    in the specification, otherwise it is 'abstract'.
  *)
  type type_decl = {
    kind: Core.kind;
    manifest: Core.def_type option;
  }

  type mod_type =
    (* sig ... end *)
    | Signature of signature
    (* functor (X : mty) mty *)
    | FunctorType of Ident.t * mod_type * mod_type

  and signature = specification list

  and specification =
    (* val x : ty *)
    | ValueSig of Ident.t * Core.val_type
    (* type t :: k [= ty] *)
    | TypeSig of Ident.t * type_decl
    (* module X : mty *)
    | ModuleSig of Ident.t * mod_type

  type mod_term =
    (* X or X.Y.Z *)
    | LongIdent of path
    (* struct ... end *)
    | Structure of structure
    (* functor (X : mty) mod *)
    | Functor of Ident.t * mod_type * mod_term
    (* mod1(mod2) *)
    | Apply of mod_term * mod_term
    (* (mod : mty) *)
    | Constraint of mod_term * mod_term

  and structure = definition list

  and definition =
    (* let x = expr *)
    | ValueStr of Ident.t * Core.term
    (* type t :: k = ty *)
    | TypeStr of Ident.t * Core.kind * Core.def_type
    (* module X = mod *)
    | ModuleStr of Ident.t * mod_term

  val subst_typedecl: type_decl -> Subst.t -> type_decl
  val subst_modtype: mod_type -> Subst.t -> mod_type

end

module Module_Syntax(Core_Syntax : CoreSyntax) = struct

  module Core = Core_Syntax

  type type_decl = {
    kind: Core.kind;
    manifest: Core.def_type option;
  }

  type mod_type =
    | Signature of signature
    | FunctorType of Ident.t * mod_type * mod_type

  and signature = specification list

  and specification =
    | ValueSig of Ident.t * Core.val_type
    | TypeSig of Ident.t * type_decl
    | ModuleSig of Ident.t * mod_type

  type mod_term =
    | LongIdent of path
    | Structure of structure
    | Functor of Ident.t * mod_type * mod_term
    | Apply of mod_term * mod_term
    | Constraint of mod_term * mod_term

  and structure = definition list

  and definition =
    | ValueStr of Ident.t * Core.term
    | TypeStr of Ident.t * Core.kind * Core.def_type
    | ModuleStr of Ident.t * mod_term

  let subst_typedecl decl sub = {
    kind = Core.subst_kind decl.kind sub;
    manifest = match decl.manifest with
      | None -> None
      | Some dty -> Some (Core.subst_deftype dty sub)
  }

  let rec subst_modtype mty sub =
    match mty with
    | Signature sg -> Signature (List.map (subst_sig_item sub) sg)
    | FunctorType (id, mty1, mty2) ->
      FunctorType (id, subst_modtype mty1 sub, subst_modtype mty2 sub)

  and subst_sig_item sub sg =
    match sg with
    | ValueSig (id, vty) -> ValueSig (id, Core.subst_valtype vty sub)
    | TypeSig (id, decl) -> TypeSig (id, subst_typedecl decl sub)
    | ModuleSig (id, mty) -> ModuleSig (id, subst_modtype mty sub)

end

module type EnvSig = sig

  module Mod : ModuleSyntax

  type t

  val empty: t
  val add_value: Ident.t -> Mod.Core.val_type -> t -> t
  val add_type: Ident.t -> Mod.type_decl -> t -> t
  val add_module: Ident.t -> Mod.mod_type -> t -> t
  val add_spec: Mod.specification -> t -> t
  val add_signature: Mod.signature -> t -> t
  val find_value: path -> t -> Mod.Core.val_type
  val find_type: path -> t -> Mod.type_decl
  val find_module: path -> t -> Mod.mod_type

end

module Env(Module_Syntax : ModuleSyntax) = struct

  module Mod = Module_Syntax

  type binding =
    | Value of Mod.Core.val_type
    | Type of Mod.type_decl
    | Module of Mod.mod_type

  type t = binding Ident.tbl

  let empty = Ident.empty_tbl

  let add_value id vty env = Ident.add id (Value vty) env

  let add_type id decl env = Ident.add id (Type decl) env

  let add_module id mty env = Ident.add id (Module mty) env

  let add_spec item env =
    match item with
    | Mod.ValueSig (id, vty) -> add_value id vty env
    | Mod.TypeSig (id, decl) -> add_type id decl env
    | Mod.ModuleSig (id, mty) -> add_module id mty env

  let add_signature = List.fold_right add_spec

  let rec find path env =
    match path with
    | PIdent id -> Ident.find id env
    | PDot (root, field) ->
      match find_module root env with
      | Mod.Signature sg -> find_field root field Subst.identity sg
      | _ -> error "structure expected in dot access"

  and find_field p field subst = function
    | [] -> error "no such field in structure"
    | Mod.ValueSig (id, vty) :: tl ->
      if Ident.name id = field
      then Value (Mod.Core.subst_valtype vty subst)
      else find_field p field subst tl
    | Mod.TypeSig (id, decl) :: tl ->
      if Ident.name id = field
      then Type (Mod.subst_typedecl decl subst)
      else find_field p field (Subst.add id (PDot (p, Ident.name id)) subst) tl
    | Mod.ModuleSig (id, mty) :: tl ->
      if Ident.name id = field
      then Module (Mod.subst_modtype mty subst)
      else find_field p field (Subst.add id (PDot (p, Ident.name id)) subst) tl

  and find_value path env =
    match find path env with
    | Value vty -> vty
    | _ -> error "value field expected"

  and find_type path env =
    match find path env with
    | Type decl -> decl
    | _ -> error "type field expected"

  and find_module path env =
    match find path env with
    | Module mty -> mty
    | _ -> error "module field expected"

end

module type CoreTyping = sig

  module Core : CoreSyntax

  module Env : EnvSig with module Mod.Core = Core

  (* Returns type of a term *)
  val type_term: Env.t -> Core.term -> Core.val_type

  (* Typing functions - Utilizes core language's typechecking *)
  val kind_deftype: Env.t -> Core.def_type -> Core.kind

  val check_valtype: Env.t -> Core.val_type -> unit

  val check_kind: Env.t -> Core.kind -> unit

  (* Type matching functions - checks structures against signatures *)
  (*
    Is t1 a subtype of t2? Can t1 be coerced to t2? Is t1 a more
    general type scheme than t2?
  *)
  val valtype_match: Env.t -> Core.val_type -> Core.val_type -> bool

  (* Are two types, viewed at kind k, equal? *)
  val deftype_equiv:
    Env.t -> Core.kind -> Core.def_type -> Core.def_type -> bool

  (* Is k1 a subkind of k2. In most languages this is an equality check *)
  val kind_match: Env.t -> Core.kind -> Core.kind -> bool

  (*
    Transforms a type path and its kind into the corresponding definable
    type. E.G. { name=u, arity=0 } => u
    { name=t, arity=2 } => ('a, 'b) -> ('a, 'b) t
  *)
  val deftype_of_path: path -> Core.kind -> Core.def_type

end

module type ModuleTyping = sig

  module Mod : ModuleSyntax

  module Env : EnvSig with module Mod = Mod

  val type_module: Env.t -> Mod.mod_term -> Mod.mod_type
  val type_definition: Env.t -> Mod.definition -> Mod.specification

end


