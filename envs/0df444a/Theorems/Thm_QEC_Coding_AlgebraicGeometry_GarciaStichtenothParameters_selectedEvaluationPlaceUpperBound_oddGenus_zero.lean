-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GarciaStichtenothParameters_selectedEvaluationPlaceUpperBound_oddGenus_zero
-- name    : QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedEvaluationPlaceUpperBound_oddGenus_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:28:06.989462+00:00
-- url     : https://prove2.me/theorems/9ac3459c-bd90-4fd1-9ada-9d78427524b4
-- title:
--   Garcia Stichtenoth Parameters: selected Evaluation Place Upper Bound odd Genus zero
-- statement:
--   At `i = 3`, the source's residue-filter argument leaves no more than this
--   many genuine evaluation places.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean#L163-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean#L163-L165

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters

theorem QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedEvaluationPlaceUpperBound_oddGenus_zero :
    selectedEvaluationPlaceUpperBound (oddGenus 0) = 1005676 := by sorry
