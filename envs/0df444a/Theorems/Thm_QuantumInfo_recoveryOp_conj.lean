-- Prove2me | Theorems.Thm_QuantumInfo_recoveryOp_conj
-- name    : QuantumInfo.recoveryOp_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:48:52.643471+00:00
-- url     : https://prove2.me/theorems/0dbac847-88e6-4006-9929-573efc239536
-- title:
--   Quantum Info: recovery Op conj
-- statement:
--   The action of one recovery operator on an error term of a code state.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L292-L312
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L292-L312

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
omit [DecidableEq n] [Fintype κ]

theorem QuantumInfo.recoveryOp_conj (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k)
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0)
    {ρ : Matrix n n ℂ} (hρ : ρ = P * ρ * P) (m k l : κ) :
    recoveryOp P F d m * (F k * ρ * (F l)ᴴ) * (recoveryOp P F d m)ᴴ
      = if m = k ∧ m = l ∧ d m ≠ 0 then ((d m : ℝ) : ℂ) • ρ else 0 := by sorry
