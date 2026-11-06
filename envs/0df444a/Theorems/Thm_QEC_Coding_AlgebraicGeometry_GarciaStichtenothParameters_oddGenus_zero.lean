-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GarciaStichtenothParameters_oddGenus_zero
-- name    : QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.oddGenus_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:26:57.185397+00:00
-- url     : https://prove2.me/theorems/aebb1461-4097-40ed-ba07-bfbae95c8cb9
-- title:
--   Garcia Stichtenoth Parameters: odd Genus zero
-- statement:
--   The first odd source level is the actual level `i = 3` genus value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean#L101-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean#L101-L102

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters

theorem QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.oddGenus_zero : oddGenus 0 = 32705 := by sorry
