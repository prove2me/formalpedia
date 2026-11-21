-- Prove2me | Theorems.Thm_QuantumInfo_IsCodeProjector_smul_injective
-- name    : QuantumInfo.IsCodeProjector.smul_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:48:17.967022+00:00
-- url     : https://prove2.me/theorems/f53b4893-b101-41e5-8054-4e10cd8e188d
-- title:
--   Is Code Projector: smul injective
-- statement:
--   A nonzero matrix determines the scalar multiplying it.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L98-L102
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L98-L102

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
open QuantumInfo.IsCodeProjector
variable {P : Matrix n n ℂ} (hP : IsCodeProjector P)
include hP
omit [Fintype n] hP

theorem QuantumInfo.IsCodeProjector.smul_injective (hP0 : P ≠ 0) {a b : ℂ} (h : a • P = b • P) : a = b := by sorry
