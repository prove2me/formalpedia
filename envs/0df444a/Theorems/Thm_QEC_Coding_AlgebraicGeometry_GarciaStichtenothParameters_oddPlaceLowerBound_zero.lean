-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GarciaStichtenothParameters_oddPlaceLowerBound_zero
-- name    : QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.oddPlaceLowerBound_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:27:47.231211+00:00
-- url     : https://prove2.me/theorems/b48098d1-520e-4830-938f-5683e85315f9
-- title:
--   Garcia Stichtenoth Parameters: odd Place Lower Bound zero
-- statement:
--   The first odd GS level's source rational-place lower bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean#L137-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean#L137-L138

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters

theorem QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.oddPlaceLowerBound_zero : oddPlaceLowerBound 0 = 1047616 := by sorry
