-- Prove2me | Theorems.Thm_QuantumInfo_exists_kraus_mul_mul_eq_smul
-- name    : QuantumInfo.exists_kraus_mul_mul_eq_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:49:15.657689+00:00
-- url     : https://prove2.me/theorems/655a6e18-3ee6-4a88-85a3-deed767ad15d
-- title:
--   Quantum Info: exists kraus mul mul eq smul
-- statement:
--   **A recovery that undoes an error up to a scalar does so Kraus operator by Kraus operator**:
--   if `R (F ρ Fᴴ) = λ • ρ` on code states, every `R.kraus k * F` acts on the code as a scalar.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L669-L683
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L669-L683

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
omit [Fintype ι] [DecidableEq ι]

theorem QuantumInfo.exists_kraus_mul_mul_eq_smul (hP : IsCodeProjector P) {κ : Type*} [Fintype κ]
    (R : Channel n n κ) {F : Matrix n n ℂ} {lam : ℂ}
    (h : ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (F * ρ * Fᴴ) = lam • ρ) (k : κ) :
    ∃ μ : ℂ, R.kraus k * F * P = μ • P := by sorry
