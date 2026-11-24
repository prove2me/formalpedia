-- Prove2me | Theorems.Thm_P2M_lh_pow_free__ffcdb6e15d31
-- name    : P2M_lh_pow_free__ffcdb6e15d31
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:47.152201+00:00
-- url     : https://prove2.me/theorems/c7f55d9f-59ca-442c-8182-e875ee56f23a
-- title:
--   P2 M lh pow free  ffcdb6e15d31: P2 M lh pow free  ffcdb6e15d31
-- statement:
--   The P2 M lh pow free  ffcdb6e15d31 construction uses the P2 M lh pow free  ffcdb6e15d31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L394-L452
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L394-L452

module
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField nonZeroDivisors
open FiniteDimensional NumberField
variable {s r : ℕ} (p : ℕ) {K : Type*} [Field K]
variable {k : Type*} [Field k] (hp : Nat.Prime p)
open Module Finset
open CyclotomicIntegers (zeta)
variable (G : Type*) [AddCommGroup G]
local notation3 "A" => CyclotomicIntegers p
variable
    [Algebra k K] (hKL : finrank k K = p) (σ : K ≃ₐ[k] K)
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
local notation "G" =>
  Additive (relativeUnitsWithGenerator p hp hKL σ hσ) ⧸
    AddCommGroup.torsion (Additive (relativeUnitsWithGenerator p hp hKL σ hσ))
local notation "mkG" => unitToU p hp hKL σ hσ
variable [NumberField k]
include hp

theorem P2M_lh_pow_free__ffcdb6e15d31 {M} [CommGroup M] [Module.Finite ℤ (Additive M)] (ν : M)
    (hk : ∀ (ε : M) (n : ℕ), ε ^ (p ^ n) = 1 → ∃ i, ν ^ i = ε)
    (r) (hr : finrank ℤ (Additive M) + 1 < r) (η : Fin r → Additive M) :
    ∃ (a : ℤ) (ι : Fin r → ℤ) (i : Fin r),
      ∑ i, ι i • η i = (a * p) • Additive.ofMul ν ∧
        ¬ ↑p ∣ ι i ∧ (ν = 1 → ↑i ≠ r - 1) := by sorry

alias «lh_pow_free'» := P2M_lh_pow_free__ffcdb6e15d31
