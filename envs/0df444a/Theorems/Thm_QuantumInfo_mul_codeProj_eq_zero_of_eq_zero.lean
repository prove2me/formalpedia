-- Prove2me | Theorems.Thm_QuantumInfo_mul_codeProj_eq_zero_of_eq_zero
-- name    : QuantumInfo.mul_codeProj_eq_zero_of_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:48:46.481365+00:00
-- url     : https://prove2.me/theorems/b842b986-43d1-48af-901c-511ae12bbda9
-- title:
--   Quantum Info: mul code Proj eq zero of eq zero
-- statement:
--   An error with `d k = 0` kills the code.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L178-L186
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L178-L186

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

theorem QuantumInfo.mul_codeProj_eq_zero_of_eq_zero (hP : IsCodeProjector P)
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0)
    {k : κ} (hk : d k = 0) : F k * P = 0 := by sorry
