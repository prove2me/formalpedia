-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GarciaStichtenothParameters_selectedEDegree_oddGenus_zero
-- name    : QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedEDegree_oddGenus_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:27:58.867553+00:00
-- url     : https://prove2.me/theorems/d1678f63-369c-4d15-9681-afabef98ba0d
-- title:
--   Garcia Stichtenoth Parameters: selected EDegree odd Genus zero
-- statement:
--   The selected `E` divisor at `i = 3` has positive degree, as required by
--   the source construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean#L152-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean#L152-L153

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters

theorem QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedEDegree_oddGenus_zero : selectedEDegree (oddGenus 0) = 8175 := by sorry
