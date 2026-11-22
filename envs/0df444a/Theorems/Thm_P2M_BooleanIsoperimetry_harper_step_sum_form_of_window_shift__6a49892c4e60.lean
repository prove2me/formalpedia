-- Prove2me | Theorems.Thm_P2M_BooleanIsoperimetry_harper_step_sum_form_of_window_shift__6a49892c4e60
-- name    : P2M_BooleanIsoperimetry_harper_step_sum_form_of_window_shift__6a49892c4e60
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:39:23.389929+00:00
-- url     : https://prove2.me/theorems/92ec3178-41d7-4f79-a770-8ff8a78f6b2c
-- title:
--   P2 M Boolean Isoperimetry harper step sum form of window shift  6a49892c4e60: P2 M Boolean Isoperimetry harper step sum form of window shift  6a49892c4e60
-- statement:
--   The P2 M Boolean Isoperimetry harper step sum form of window shift  6a49892c4e60 construction uses the P2 M Boolean Isoperimetry harper step sum form of window shift  6a49892c4e60 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L180-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L180-L192

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem P2M_BooleanIsoperimetry_harper_step_sum_form_of_window_shift__6a49892c4e60 (n : ℕ)
    {a b p q : ℕ}
    (hpa : p ≤ a) (hbq : b ≤ q)
    (hwin :
      gShiftIntervalCount (n + 1) b q ≤
        gShiftIntervalCount (n + 1) p a) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + H (n + 1) b := by sorry

alias «BooleanIsoperimetry».«harper_step_sum_form_of_window_shift'» := P2M_BooleanIsoperimetry_harper_step_sum_form_of_window_shift__6a49892c4e60
