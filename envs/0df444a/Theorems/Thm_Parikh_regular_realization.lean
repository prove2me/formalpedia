-- Prove2me | Theorems.Thm_Parikh_regular_realization
-- name    : Parikh.regular_realization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:52:00.280122+00:00
-- url     : https://prove2.me/theorems/8fce7c43-be8f-4f8b-8afa-079189aba4af
-- title:
--   Parikh: regular realization
-- statement:
--   Every CFL has a DFA-regular language with the same image (`thm:parikh-statement`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Statements.lean#L64-L66
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Statements.lean#L64-L66

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

theorem Parikh.regular_realization [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    ∃ R : Language T, R.IsRegular ∧ image R = image g.language := by sorry
