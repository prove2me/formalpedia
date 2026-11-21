-- Prove2me | Theorems.Thm_QuantumInfo_conjTranspose_mul_mul_conjTranspose
-- name    : QuantumInfo.conjTranspose_mul_mul_conjTranspose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:50:33.060066+00:00
-- url     : https://prove2.me/theorems/7ffb5644-c52b-4623-b871-b55264abc4bc
-- title:
--   Quantum Info: conj Transpose mul mul conj Transpose
-- statement:
--   The Quantum Info construction uses the conj Transpose mul mul conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L758-L759
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L758-L759

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
omit [DecidableEq n]

theorem QuantumInfo.conjTranspose_mul_mul_conjTranspose (hV : Vᴴ * V = 1) : Vᴴ * (V * Vᴴ) = Vᴴ := by sorry
