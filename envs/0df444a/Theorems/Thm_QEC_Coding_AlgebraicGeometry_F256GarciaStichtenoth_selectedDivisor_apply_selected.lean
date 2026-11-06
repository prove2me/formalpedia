-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_selectedDivisor_apply_selected
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedDivisor_apply_selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:15:34.924211+00:00
-- url     : https://prove2.me/theorems/dd6c783f-3f9b-4f9a-ac9f-d841440e8dfa
-- title:
--   F256 Garcia Stichtenoth: selected Divisor apply selected
-- statement:
--   Every enumerated selected place has coefficient one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Divisors.lean#L28-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Divisors.lean#L28-L41

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Enumeration
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Divisors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedDivisor_apply_selected (i : ℕ)
    (j : Fin (selectedLength i)) :
    selectedDivisor i (selectedPlace i j) = 1 := by sorry
