-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveDeterminant_conjugate_mem_specialProjectiveSubgroup
-- name    : QEC.Coding.ExpanderCodes.ProjectiveDeterminant.conjugate_mem_specialProjectiveSubgroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:47:04.977208+00:00
-- url     : https://prove2.me/theorems/29bf37ef-9ec7-4fb9-a8e7-69c86805b631
-- title:
--   Projective Determinant: conjugate mem special Projective Subgroup
-- statement:
--   The determinant-square subgroup is invariant under every projective conjugation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProjectiveDeterminant.lean#L77-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProjectiveDeterminant.lean#L77-L86

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveDeterminant
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.ProjectiveDeterminant
open Matrix
variable {K : Type*} [Field K]

theorem QEC.Coding.ExpanderCodes.ProjectiveDeterminant.conjugate_mem_specialProjectiveSubgroup (c g : Matrix.ProjGenLinGroup (Fin 2) K)
    (hg : g ∈ specialProjectiveSubgroup) :
    c * g * c⁻¹ ∈ specialProjectiveSubgroup := by sorry
