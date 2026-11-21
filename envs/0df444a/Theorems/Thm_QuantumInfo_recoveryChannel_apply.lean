-- Prove2me | Theorems.Thm_QuantumInfo_recoveryChannel_apply
-- name    : QuantumInfo.recoveryChannel_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:48:56.433765+00:00
-- url     : https://prove2.me/theorems/0eddc582-4e67-4565-90ef-a0ae6dc24398
-- title:
--   Quantum Info: recovery Channel apply
-- statement:
--   **The recovery channel undoes an orthogonal error family on the code**:
--   `R (F k ρ F lᴴ) = d k δ_kl • ρ` for `ρ = P ρ P`.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L342-L378
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L342-L378

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
variable {κ : Type*} [DecidableEq κ]
variable (P : Matrix n n ℂ) (F : κ → Matrix n n ℂ) (d : κ → ℝ)
variable [Fintype κ]
variable {P F d}

theorem QuantumInfo.recoveryChannel_apply (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k)
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0)
    {ρ : Matrix n n ℂ} (hρ : ρ = P * ρ * P) (k l : κ) :
    (recoveryChannel hP hd hF).apply (F k * ρ * (F l)ᴴ)
      = if k = l then ((d k : ℝ) : ℂ) • ρ else 0 := by sorry
