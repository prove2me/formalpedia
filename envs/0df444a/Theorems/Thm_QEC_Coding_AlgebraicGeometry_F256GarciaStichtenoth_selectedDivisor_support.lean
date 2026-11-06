-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_selectedDivisor_support
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedDivisor_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:15:29.45635+00:00
-- url     : https://prove2.me/theorems/29ba54a7-1074-43e0-9bf9-9cce502fd343
-- title:
--   F256 Garcia Stichtenoth: selected Divisor support
-- statement:
--   The support of the selected-place divisor is exactly the selected finite
--   set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Divisors.lean#L70-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Divisors.lean#L70-L83

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Enumeration
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Divisors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedDivisor_support (i : ℕ) :
    (selectedDivisor i).support = selectedPlaces i := by sorry
