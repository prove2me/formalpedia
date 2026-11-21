-- Prove2me | Theorems.Thm_QuantumInfo_exists_smul_recovery_apply_of_eq_lin_comb
-- name    : QuantumInfo.exists_smul_recovery_apply_of_eq_lin_comb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:49:56.676347+00:00
-- url     : https://prove2.me/theorems/36c73e46-413e-4400-9a55-433a26060c65
-- title:
--   Quantum Info: exists smul recovery apply of eq lin comb
-- statement:
--   The same statement for an error given as a linear combination: if `F` is a combination of the
--   `E i`, the recovery returns a multiple of the code state.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L554-L561
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L554-L561

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

theorem QuantumInfo.exists_smul_recovery_apply_of_eq_lin_comb {κ : Type*} [Fintype κ] {R : Channel n n κ}
    (hR : ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P →
      ∀ i j, R.apply (E i * ρ * (E j)ᴴ) = c j i • ρ)
    {F : Matrix n n ℂ} {a : ι → ℂ} (hF : F = ∑ i, a i • E i) :
    ∃ γ : ℂ, ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (F * ρ * Fᴴ) = γ • ρ := by sorry
