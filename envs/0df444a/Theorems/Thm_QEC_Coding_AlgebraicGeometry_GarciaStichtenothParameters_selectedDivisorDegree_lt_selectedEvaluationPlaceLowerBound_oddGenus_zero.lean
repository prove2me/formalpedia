-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GarciaStichtenothParameters_selectedDivisorDegree_lt_selectedEvaluationPlaceLowerBound_oddGenus_zero
-- name    : QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedDivisorDegree_lt_selectedEvaluationPlaceLowerBound_oddGenus_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:28:04.056236+00:00
-- url     : https://prove2.me/theorems/a234abec-9130-4f3a-b52d-cf2539a1a17c
-- title:
--   Garcia Stichtenoth Parameters: selected Divisor Degree lt selected Evaluation Place Lower Bound odd Genus zero
-- statement:
--   The exact `i = 3` lower evaluation-place budget exceeds the selected
--   divisor degree, which is the numerical part of evaluation injectivity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean#L169-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean#L169-L172

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters

theorem QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedDivisorDegree_lt_selectedEvaluationPlaceLowerBound_oddGenus_zero :
    selectedDivisorDegree (oddGenus 0) < selectedEvaluationPlaceLowerBound (oddGenus 0) := by sorry
