-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GarciaStichtenothParameters_selectedCodeDimension_oddGenus_zero
-- name    : QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedCodeDimension_oddGenus_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:27:36.626256+00:00
-- url     : https://prove2.me/theorems/838f9ca5-e3c9-4e88-a355-bd31820a267f
-- title:
--   Garcia Stichtenoth Parameters: selected Code Dimension odd Genus zero
-- statement:
--   The `i = 3` pre-puncture AG-code dimension is derived from its selected
--   divisor degree and closed genus formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean#L126-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean#L126-L127

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters

theorem QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedCodeDimension_oddGenus_zero : selectedCodeDimension (oddGenus 0) = 114468 := by sorry
