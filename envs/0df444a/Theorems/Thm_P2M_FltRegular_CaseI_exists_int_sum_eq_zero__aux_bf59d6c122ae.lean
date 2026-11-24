-- Prove2me | Theorems.Thm_P2M_FltRegular_CaseI_exists_int_sum_eq_zero__aux_bf59d6c122ae
-- name    : P2M_FltRegular_CaseI_exists_int_sum_eq_zero__aux_bf59d6c122ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:35:49.726804+00:00
-- url     : https://prove2.me/theorems/be4f62c2-a163-4cbf-9ea7-796a73674182
-- title:
--   P2 M Flt Regular Case I exists int sum eq zero  aux bf59d6c122ae: P2 M Flt Regular Case I exists int sum eq zero  aux bf59d6c122ae
-- statement:
--   Complex conjugation negates the exponent of the distinguished cyclotomic unit.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/CaseI.lean#L45-L59
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/CaseI.lean#L45-L59

module
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_UnitLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CaseI
set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField nonZeroDivisors
variable {p : ℕ} [NeZero p] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
local notation3 "zetaUnit" => (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit
open FractionalIdeal NumberField IsCMField
open FltRegular FltRegular.CaseI

theorem P2M_FltRegular_CaseI_exists_int_sum_eq_zero__aux_bf59d6c122ae (x y i : ℤ) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    ringOfIntegersComplexConj K (x + y * ↑(zetaUnit ^ i) : 𝓞 K) =
      x + y * (zetaUnit ^ (-i) : (𝓞 K)ˣ) := by sorry

alias «FltRegular».«CaseI».«exists_int_sum_eq_zero'_aux» := P2M_FltRegular_CaseI_exists_int_sum_eq_zero__aux_bf59d6c122ae
