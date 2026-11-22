-- Prove2me | Theorems.Thm_Parikh_regular_image
-- name    : Parikh.regular_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:49.703802+00:00
-- url     : https://prove2.me/theorems/aec98d9a-1f5c-4399-b280-ee7e1b7879cd
-- title:
--   Parikh: regular image
-- statement:
--   Regular-language specialization using Mathlib's DFA semantics (`thm:parikh-statement`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L268-L275
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L268-L275

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_DFAGrammar
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata
public import Definitions.Def_LeanPool_Parikh_RegularRealization
set_option autoImplicit true
@[expose] public section
public section
open scoped Computability Pointwise
open Parikh
variable {T : Type*}

theorem Parikh.regular_image [Finite T] [DecidableEq T] (R : Language T) (hR : R.IsRegular) :
    IsSemilinearSet (image R) := by sorry
