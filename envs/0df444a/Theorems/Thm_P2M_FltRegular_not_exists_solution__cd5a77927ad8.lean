-- Prove2me | Theorems.Thm_P2M_FltRegular_not_exists_solution__cd5a77927ad8
-- name    : P2M_FltRegular_not_exists_solution__cd5a77927ad8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:14:13.913592+00:00
-- url     : https://prove2.me/theorems/c863ebee-b352-4a06-8053-9eee838c2516
-- title:
--   P2 M Flt Regular not exists solution  cd5a77927ad8: P2 M Flt Regular not exists solution  cd5a77927ad8
-- statement:
--   The P2 M Flt Regular not exists solution  cd5a77927ad8 construction uses the P2 M Flt Regular not exists solution  cd5a77927ad8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseII/Statement.lean#L35-L49
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseII/Statement.lean#L35-L49

module
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_CaseII_InductionStep
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Definitions.Def_FltRegular_CaseII_Statement
set_option autoImplicit false
@[expose] public section
public section
open scoped nonZeroDivisors NumberField
open Polynomial
variable {K : Type} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] (hp : p ≠ 2) [Fintype (ClassGroup (𝓞 K))]
  (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
open FltRegular
include hp hreg

theorem P2M_FltRegular_not_exists_solution__cd5a77927ad8 : ¬∃ (x y z : 𝓞 K), ¬(hζ.toInteger : 𝓞 K) - 1 ∣ y ∧
    (hζ.toInteger : 𝓞 K) - 1 ∣ z ∧ z ≠ 0 ∧ x ^ p + y ^ p = z ^ p := by sorry

alias «FltRegular».«not_exists_solution'» := P2M_FltRegular_not_exists_solution__cd5a77927ad8
