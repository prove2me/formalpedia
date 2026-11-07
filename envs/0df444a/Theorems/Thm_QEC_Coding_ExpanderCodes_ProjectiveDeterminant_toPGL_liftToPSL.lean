-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveDeterminant_toPGL_liftToPSL
-- name    : QEC.Coding.ExpanderCodes.ProjectiveDeterminant.toPGL_liftToPSL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:44:40.626302+00:00
-- url     : https://prove2.me/theorems/4c7a5851-b457-4756-a21d-32bcaa824be7
-- title:
--   Projective Determinant: to PGL lift To PSL
-- statement:
--   The Projective Determinant construction uses the to PGL lift To PSL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProjectiveDeterminant.lean#L94-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProjectiveDeterminant.lean#L94-L97

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveDeterminant
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.ProjectiveDeterminant
open Matrix
variable {K : Type*} [Field K]

theorem QEC.Coding.ExpanderCodes.ProjectiveDeterminant.toPGL_liftToPSL (g : Matrix.ProjGenLinGroup (Fin 2) K)
    (hg : g ∈ specialProjectiveSubgroup) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (liftToPSL g hg) = g := by sorry
