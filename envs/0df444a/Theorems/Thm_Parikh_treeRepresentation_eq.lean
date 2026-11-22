-- Prove2me | Theorems.Thm_Parikh_treeRepresentation_eq
-- name    : Parikh.treeRepresentation_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:52:48.41921+00:00
-- url     : https://prove2.me/theorems/62c98cb8-e200-44a8-936f-bc466cb7797e
-- title:
--   Parikh: tree Representation eq
-- statement:
--   The exact tree/context union equals the Mathlib grammar image (`thm:main`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Statements.lean#L41-L43
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Statements.lean#L41-L43

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}

theorem Parikh.treeRepresentation_eq [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    treeRepresentation g = image g.language := by sorry
