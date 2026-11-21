-- Prove2me | Theorems.Thm_QuantumInfo_mul_conjTranspose_ne_zero
-- name    : QuantumInfo.mul_conjTranspose_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:49:22.247398+00:00
-- url     : https://prove2.me/theorems/5c4a61dc-f4f8-44fd-affe-1b7a2eb4ea3a
-- title:
--   Quantum Info: mul conj Transpose ne zero
-- statement:
--   The code of an isometric encoder is nonzero as soon as it encodes something.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L741-L751
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L741-L751

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

theorem QuantumInfo.mul_conjTranspose_ne_zero [Nonempty L] (hV : Vᴴ * V = 1) : V * Vᴴ ≠ 0 := by sorry
