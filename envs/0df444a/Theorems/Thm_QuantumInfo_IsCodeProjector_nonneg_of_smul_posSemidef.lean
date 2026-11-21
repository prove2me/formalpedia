-- Prove2me | Theorems.Thm_QuantumInfo_IsCodeProjector_nonneg_of_smul_posSemidef
-- name    : QuantumInfo.IsCodeProjector.nonneg_of_smul_posSemidef
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:48:35.027188+00:00
-- url     : https://prove2.me/theorems/5850776b-7b7f-4e78-bb98-423d7ffd6a6e
-- title:
--   Is Code Projector: nonneg of smul pos Semidef
-- statement:
--   A real scalar `a` with `a • P` positive semidefinite is nonnegative.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L105-L112
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/KnillLaflamme.lean#L105-L112

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

theorem QuantumInfo.IsCodeProjector.nonneg_of_smul_posSemidef (hP0 : P ≠ 0) {a : ℝ}
    (h : ((a : ℂ) • P).PosSemidef) : 0 ≤ a := by sorry
