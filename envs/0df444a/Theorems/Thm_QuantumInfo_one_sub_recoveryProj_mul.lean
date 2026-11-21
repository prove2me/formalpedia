-- Prove2me | Theorems.Thm_QuantumInfo_one_sub_recoveryProj_mul
-- name    : QuantumInfo.one_sub_recoveryProj_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:48:54.878403+00:00
-- url     : https://prove2.me/theorems/5af1855b-0aa9-47db-b4b2-81617de983f7
-- title:
--   Quantum Info: one sub recovery Proj mul
-- statement:
--   The completion `1 − Q` kills every error image of the code.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L315-L338
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L315-L338

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

theorem QuantumInfo.one_sub_recoveryProj_mul (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k)
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0) (k : κ) :
    (1 - recoveryProj P F d) * F k * P = 0 := by sorry
