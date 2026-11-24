-- Prove2me | Theorems.Thm_P2M_FltRegular_CaseI_exists_int_sum_eq_zero__050f4fd83c8a
-- name    : P2M_FltRegular_CaseI_exists_int_sum_eq_zero__050f4fd83c8a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:35:45.106285+00:00
-- url     : https://prove2.me/theorems/becdb6b4-648c-4f1b-bb05-14fda90c939d
-- title:
--   P2 M Flt Regular Case I exists int sum eq zero  050f4fd83c8a: P2 M Flt Regular Case I exists int sum eq zero  050f4fd83c8a
-- statement:
--   A natural exponent giving the Case I complex-conjugation congruence modulo `p`.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/CaseI.lean#L62-L78
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/CaseI.lean#L62-L78

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

theorem P2M_FltRegular_CaseI_exists_int_sum_eq_zero__050f4fd83c8a (x y i : ℤ) {u : (𝓞 K)ˣ} {α : 𝓞 K}
    (h : (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) = u * α ^ p) [Fact (p.Prime)]
    (hp : 2 < p) :
    ∃ k : ℕ, (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) -
      ((zetaUnit ^ k) ^ 2 : (𝓞 K)ˣ) *
        (x + y * (zetaUnit ^ (-i) : (𝓞 K)ˣ)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by sorry

alias «FltRegular».«CaseI».«exists_int_sum_eq_zero'» := P2M_FltRegular_CaseI_exists_int_sum_eq_zero__050f4fd83c8a
