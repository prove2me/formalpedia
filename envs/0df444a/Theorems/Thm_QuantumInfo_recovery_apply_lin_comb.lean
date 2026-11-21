-- Prove2me | Theorems.Thm_QuantumInfo_recovery_apply_lin_comb
-- name    : QuantumInfo.recovery_apply_lin_comb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:49:10.489647+00:00
-- url     : https://prove2.me/theorems/34a22efe-b447-43fe-a9b2-dc5366cc7633
-- title:
--   Quantum Info: recovery apply lin comb
-- statement:
--   **The recovery corrects every linear combination of the error operators**, up to the scalar
--   its coefficients give. This is the discretization step: a code that corrects finitely many errors
--   corrects the whole subspace they span, because the correction property is sesquilinear in the two
--   error slots (conjugate-linear in the second) and the recovery is linear. Correcting the four Paulis
--   on a qubit therefore corrects *every* operator on that qubit.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L538-L549
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L538-L549

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
set_option autoImplicit false
@[expose] public section
public section
open Matrix Unitary
open scoped ComplexOrder ComplexConjugate
open QuantumInfo
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Matrix n n ℂ} {E : ι → Matrix n n ℂ} {c : Matrix ι ι ℂ}
omit [DecidableEq ι]

theorem QuantumInfo.recovery_apply_lin_comb {κ : Type*} [Fintype κ] {R : Channel n n κ}
    (hR : ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P →
      ∀ i j, R.apply (E i * ρ * (E j)ᴴ) = c j i • ρ)
    (a : ι → ℂ) {ρ : Matrix n n ℂ} (hρ : ρ = P * ρ * P) :
    R.apply ((∑ i, a i • E i) * ρ * (∑ i, a i • E i)ᴴ)
      = (∑ i, ∑ j, star (a i) * a j * c i j) • ρ := by sorry
