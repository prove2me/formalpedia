-- Prove2me | Theorems.Thm_QuantumInfo_recoveryOp_mul_mul_codeProj
-- name    : QuantumInfo.recoveryOp_mul_mul_codeProj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:48:51.558535+00:00
-- url     : https://prove2.me/theorems/6d524050-001d-4fa6-b7fa-aeeb8e5d4a25
-- title:
--   Quantum Info: recovery Op mul mul code Proj
-- statement:
--   The Quantum Info construction uses the recovery Op mul mul code Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L276-L288
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L276-L288

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

theorem QuantumInfo.recoveryOp_mul_mul_codeProj
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0) (m k : κ) :
    recoveryOp P F d m * F k * P
      = if m = k ∧ d m ≠ 0 then ((Real.sqrt (d m) : ℝ) : ℂ) • P else 0 := by sorry
