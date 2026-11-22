-- Prove2me | Theorems.Thm_Parikh_exists_boundedSemilinearRepresentation_of_grammar
-- name    : Parikh.exists_boundedSemilinearRepresentation_of_grammar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:56:58.038961+00:00
-- url     : https://prove2.me/theorems/185e4de7-91f3-40e9-920a-344cff911e11
-- title:
--   Parikh: exists bounded Semilinear Representation of grammar
-- statement:
--   An exact representation also exists within the grammar's size bounds.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Api.lean#L84-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Api.lean#L84-L87

module
public import Definitions.Def_LeanPool_Parikh_ExecutableCompiler
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
public import Definitions.Def_LeanPool_Parikh_Api
set_option autoImplicit true
@[expose] public section
public section
open Parikh

theorem Parikh.exists_boundedSemilinearRepresentation_of_grammar {T : Type*}
    [Fintype T] [DecidableEq T] (g : ContextFreeGrammar T) :
    ∃ W : SemilinearRepresentation T,
      W.denotation = parikhImage g.language ∧ WithinBounds (grammarSize g) W := by sorry
