-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GarciaStichtenothParameters_selectedEvaluationPlaceLowerBound_oddGenus_zero
-- name    : QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedEvaluationPlaceLowerBound_oddGenus_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:28:10.029699+00:00
-- url     : https://prove2.me/theorems/5fb321d4-c856-4e41-8cf2-d04b2ea49bcd
-- title:
--   Garcia Stichtenoth Parameters: selected Evaluation Place Lower Bound odd Genus zero
-- statement:
--   At `i = 3`, the source's residue-filter argument leaves at least this
--   many genuine evaluation places once its tower/place construction is supplied.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean#L157-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean#L157-L159

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters

theorem QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedEvaluationPlaceLowerBound_oddGenus_zero :
    selectedEvaluationPlaceLowerBound (oddGenus 0) = 972971 := by sorry
