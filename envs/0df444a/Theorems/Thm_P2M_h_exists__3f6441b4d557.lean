-- Prove2me | Theorems.Thm_P2M_h_exists__3f6441b4d557
-- name    : P2M_h_exists__3f6441b4d557
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:17.145401+00:00
-- url     : https://prove2.me/theorems/6416a8bf-37d5-4adc-9303-cf018979b5a6
-- title:
--   P2 M h exists  3f6441b4d557: P2 M h exists  3f6441b4d557
-- statement:
--   The P2 M h exists  3f6441b4d557 construction uses the P2 M h exists  3f6441b4d557 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L599-L616
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L599-L616

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
variable [NumberField K]
variable [IsGalois k K]
attribute [local instance] _p2m_local_instance_fee6646a52_507
attribute [local instance] _p2m_local_instance_fee6646a52_512
attribute [local instance] _p2m_local_instance_fee6646a52_515
variable [IsUnramifiedAtInfinitePlaces k K]
include hp

theorem P2M_h_exists__3f6441b4d557 : ∃ (h : ℕ) (ν : (𝓞 k)ˣ), IsPrimitiveRoot (ν : k) (p ^ h) ∧
    ∀ (ε : (𝓞 k)ˣ) (n : ℕ), ε ^ (p ^ n) = 1 → ∃ i, ν ^ i = ε := by sorry

alias «h_exists'» := P2M_h_exists__3f6441b4d557
