-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveDeterminant_mk_mem_specialProjectiveSubgroup_iff
-- name    : QEC.Coding.ExpanderCodes.ProjectiveDeterminant.mk_mem_specialProjectiveSubgroup_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:44:26.570564+00:00
-- url     : https://prove2.me/theorems/28d83145-9dad-41f4-a2c4-ddb5485997ea
-- title:
--   Projective Determinant: mk mem special Projective Subgroup iff
-- statement:
--   A matrix class has a determinant-one representative precisely when its
--   unit determinant has an actual square root.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProjectiveDeterminant.lean#L36-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProjectiveDeterminant.lean#L36-L58

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveDeterminant
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.ProjectiveDeterminant
open Matrix
variable {K : Type*} [Field K]

theorem QEC.Coding.ExpanderCodes.ProjectiveDeterminant.mk_mem_specialProjectiveSubgroup_iff (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Matrix.ProjGenLinGroup.mk g ∈ specialProjectiveSubgroup ↔
      ∃ r : Kˣ, r ^ 2 = Matrix.GeneralLinearGroup.det g := by sorry
