-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceRecursionStep_finrank
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceRecursionStep_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:56:08.497197+00:00
-- url     : https://prove2.me/theorems/217eeb89-7eb2-4cee-bd0b-cfb001e22854
-- title:
--   F256 Garcia Stichtenoth: source Recursion Step finrank
-- statement:
--   Every actual source-recursion step has degree sixteen.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRecursion.lean#L141-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRecursion.lean#L141-L144

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Mathlib.NumberTheory.FunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceRecursionStep_finrank (i : ℕ) :
    Module.finrank (SourceField i) (SourceField (i + 1)) = 16 := by sorry
