-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_selectedDivisor_apply_eq_zero_of_not_mem
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedDivisor_apply_eq_zero_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:16:12.957494+00:00
-- url     : https://prove2.me/theorems/75e05212-e6a0-4b5a-9453-f83c87142fbe
-- title:
--   F256 Garcia Stichtenoth: selected Divisor apply eq zero of not mem
-- statement:
--   A place outside the selected finite set has coefficient zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Divisors.lean#L44-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Divisors.lean#L44-L57

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Enumeration
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Divisors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedDivisor_apply_eq_zero_of_not_mem (i : ℕ)
    (P : GlobalPlace F256 (Field (i + 2))) (hP : P ∉ selectedPlaces i) :
    selectedDivisor i P = 0 := by sorry
