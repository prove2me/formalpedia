-- Prove2me | Theorems.Thm_QuantumInfo_encoderKL_iff
-- name    : QuantumInfo.encoderKL_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:49:26.940902+00:00
-- url     : https://prove2.me/theorems/c5c5942c-d3cc-4e32-bdac-a17f1da1ae32
-- title:
--   Quantum Info: encoder KL iff
-- statement:
--   The Quantum Info construction uses the encoder KL iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L805-L806
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L805-L806

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
variable {L : Type*} [Fintype L] [DecidableEq L] {V : Matrix n L ℂ}
omit [DecidableEq n] [Fintype ι] [DecidableEq ι] [Fintype L]

theorem QuantumInfo.encoderKL_iff {E : ι → Matrix n n ℂ} :
    EncoderKL V E ↔ ∀ i j, ∃ γ : ℂ, Vᴴ * (E i)ᴴ * E j * V = γ • 1 := by sorry
