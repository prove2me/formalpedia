-- Prove2me | Theorems.Thm_QuantumInfo_mul_conjTranspose_mul_encoder
-- name    : QuantumInfo.mul_conjTranspose_mul_encoder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:50:20.976367+00:00
-- url     : https://prove2.me/theorems/0b8f9681-e960-4d2b-a781-10d9fe733c9d
-- title:
--   Quantum Info: mul conj Transpose mul encoder
-- statement:
--   The Quantum Info construction uses the mul conj Transpose mul encoder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L754-L755
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L754-L755

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

theorem QuantumInfo.mul_conjTranspose_mul_encoder (hV : Vᴴ * V = 1) : V * Vᴴ * V = V := by sorry
