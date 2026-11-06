-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GarciaStichtenothParameters_selectedPhysicalLengthUpperBound_oddGenus_zero
-- name    : QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedPhysicalLengthUpperBound_oddGenus_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:27:50.454774+00:00
-- url     : https://prove2.me/theorems/7ff65481-c95b-4b6f-9147-9cb8af77be68
-- title:
--   Garcia Stichtenoth Parameters: selected Physical Length Upper Bound odd Genus zero
-- statement:
--   The `i = 3` upper physical-length expression in WHY24's sandwich.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean#L146-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean#L146-L148

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters

theorem QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters.selectedPhysicalLengthUpperBound_oddGenus_zero :
    selectedPhysicalLengthUpperBound (oddGenus 0) = 964796 := by sorry
