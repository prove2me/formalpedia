-- Prove2me | Theorems.Thm_QuantumInfo_isCodeProjector_mul_conjTranspose
-- name    : QuantumInfo.isCodeProjector_mul_conjTranspose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:49:19.370613+00:00
-- url     : https://prove2.me/theorems/eb3de67a-d5dc-4f70-a764-bd326a243358
-- title:
--   Quantum Info: is Code Projector mul conj Transpose
-- statement:
--   An isometric encoder gives a code projector: `P = V Vᴴ` for `Vᴴ V = 1`.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L733-L737
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L733-L737

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

theorem QuantumInfo.isCodeProjector_mul_conjTranspose (hV : Vᴴ * V = 1) : IsCodeProjector (V * Vᴴ) := by sorry
