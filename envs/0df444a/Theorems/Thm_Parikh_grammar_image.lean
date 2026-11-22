-- Prove2me | Theorems.Thm_Parikh_grammar_image
-- name    : Parikh.grammar_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:26.732546+00:00
-- url     : https://prove2.me/theorems/086787c6-e9c7-4f79-aecd-66f1fea8a2f1
-- title:
--   Parikh: grammar image
-- statement:
--   Forward Parikh theorem for Mathlib grammars (`thm:parikh-statement`).
--   No finiteness or decidable-equality assumption is imposed on `g.NT`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Statements.lean#L48-L50
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Statements.lean#L48-L50

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

theorem Parikh.grammar_image [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    IsSemilinearSet (image g.language) := by sorry
