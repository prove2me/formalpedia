-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GarciaStichtenothParameters_selectedDistanceLowerBound_oddGenus_zero
-- name    : QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedDistanceLowerBound_oddGenus_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:27:42.959375+00:00
-- url     : https://prove2.me/theorems/255ccb45-aeca-4ca1-92f6-f5652f737b5b
-- title:
--   Garcia Stichtenoth Parameters: selected Distance Lower Bound odd Genus zero
-- statement:
--   The `i = 3` source distance lower bound is derived arithmetically, not
--   stored as a distance claim about an unconstructed code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean#L131-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean#L131-L134

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters

theorem QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedDistanceLowerBound_oddGenus_zero :
    selectedDistanceLowerBound (oddGenus 0) = 40883 := by sorry
