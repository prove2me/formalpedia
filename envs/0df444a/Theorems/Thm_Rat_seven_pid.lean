-- Prove2me | Theorems.Thm_Rat_seven_pid
-- name    : Rat.seven_pid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:39:09.243719+00:00
-- url     : https://prove2.me/theorems/1f1d4471-60c2-4e08-8909-f7662e97fd23
-- title:
--   Rat: seven pid
-- statement:
--   The ring of integers of a seventh-cyclotomic number field is a principal ideal domain.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/SmallNumbers/Seven/Seven.lean#L60-L78
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/SmallNumbers/Seven/Seven.lean#L60-L78

module
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_FltRegular_SmallNumbers_Seven_Seven
set_option autoImplicit false
@[expose] public section
public section
open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers
  IsCyclotomicExtension.Rat Polynomial cyclotomic Ideal
variable {K : Type*} [Field K] [NumberField K]
local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)
variable [IsCyclotomicExtension {7} ℚ K]
variable (K)

theorem Rat.seven_pid : IsPrincipalIdealRing (𝓞 K) := by sorry
