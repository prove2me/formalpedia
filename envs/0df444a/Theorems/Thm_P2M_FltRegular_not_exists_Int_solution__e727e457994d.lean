-- Prove2me | Theorems.Thm_P2M_FltRegular_not_exists_Int_solution__e727e457994d
-- name    : P2M_FltRegular_not_exists_Int_solution__e727e457994d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:13:56.660473+00:00
-- url     : https://prove2.me/theorems/adf3a6f8-efaf-4925-a657-c7c3589db381
-- title:
--   P2 M Flt Regular not exists Int solution  e727e457994d: P2 M Flt Regular not exists Int solution  e727e457994d
-- statement:
--   The P2 M Flt Regular not exists Int solution  e727e457994d construction uses the P2 M Flt Regular not exists Int solution  e727e457994d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseII/Statement.lean#L66-L78
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseII/Statement.lean#L66-L78

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

theorem P2M_FltRegular_not_exists_Int_solution__e727e457994d {p : ℕ} [hpri : Fact (Nat.Prime p)] (hreg : IsRegularPrime p)
    (hodd : p ≠ 2) :
    ¬∃ (x y z : ℤ), ({x, y, z} : Finset ℤ).gcd id = 1 ∧ ↑p ∣ z ∧ z ≠ 0 ∧
      x ^ p + y ^ p = z ^ p := by sorry

alias «FltRegular».«not_exists_Int_solution'» := P2M_FltRegular_not_exists_Int_solution__e727e457994d
