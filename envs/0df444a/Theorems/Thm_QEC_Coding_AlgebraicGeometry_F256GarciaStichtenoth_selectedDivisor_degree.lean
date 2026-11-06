-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_selectedDivisor_degree
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedDivisor_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:16:22.79524+00:00
-- url     : https://prove2.me/theorems/b385a36b-2867-47b6-8771-d38c8d686426
-- title:
--   F256 Garcia Stichtenoth: selected Divisor degree
-- statement:
--   The weighted degree of the selected-place divisor is the exact selected
--   length because every selected place is rational.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Divisors.lean#L94-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Divisors.lean#L94-L117

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Enumeration
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Divisors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedDivisor_degree (i : ℕ) :
    Divisor.degree GlobalPlace.residueDegree (selectedDivisor i) =
      selectedLength i := by sorry
