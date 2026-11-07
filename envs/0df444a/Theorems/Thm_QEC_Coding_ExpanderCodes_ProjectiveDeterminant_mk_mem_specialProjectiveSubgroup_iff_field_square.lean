-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveDeterminant_mk_mem_specialProjectiveSubgroup_iff_field_square
-- name    : QEC.Coding.ExpanderCodes.ProjectiveDeterminant.mk_mem_specialProjectiveSubgroup_iff_field_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:44:41.447907+00:00
-- url     : https://prove2.me/theorems/c4922b94-ca59-42f8-a365-8c28cb7a50a2
-- title:
--   Projective Determinant: mk mem special Projective Subgroup iff field square
-- statement:
--   The unit-square criterion is equivalent to the usual field-square criterion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProjectiveDeterminant.lean#L61-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProjectiveDeterminant.lean#L61-L74

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveDeterminant
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.ProjectiveDeterminant
open Matrix
variable {K : Type*} [Field K]

theorem QEC.Coding.ExpanderCodes.ProjectiveDeterminant.mk_mem_specialProjectiveSubgroup_iff_field_square
    (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Matrix.ProjGenLinGroup.mk g ∈ specialProjectiveSubgroup ↔
      ∃ r : K, r ^ 2 = (Matrix.GeneralLinearGroup.det g : K) := by sorry
