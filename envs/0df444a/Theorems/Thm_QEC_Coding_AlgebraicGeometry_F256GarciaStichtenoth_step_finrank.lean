-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_step_finrank
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.step_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:07:28.945789+00:00
-- url     : https://prove2.me/theorems/b2468277-f44b-48b9-928b-beae84a2818a
-- title:
--   F256 Garcia Stichtenoth: step finrank
-- statement:
--   Every actual recursion step has degree sixteen.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Recursion.lean#L140-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Recursion.lean#L140-L143

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Mathlib.NumberTheory.FunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Recursion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.step_finrank (i : ℕ) :
    Module.finrank (Field i) (Field (i + 1)) = 16 := by sorry
