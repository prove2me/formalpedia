-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GarciaStichtenothParameters_selectedDecodingRadius_oddGenus_zero
-- name    : QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedDecodingRadius_oddGenus_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:27:32.200274+00:00
-- url     : https://prove2.me/theorems/87d37624-6cd5-458f-988a-bf6770a9c75a
-- title:
--   Garcia Stichtenoth Parameters: selected Decoding Radius odd Genus zero
-- statement:
--   The `i = 3` candidate decoding radius is derived from the genus formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean#L121-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean#L121-L122

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters

theorem QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedDecodingRadius_oddGenus_zero : selectedDecodingRadius (oddGenus 0) = 4088 := by sorry
