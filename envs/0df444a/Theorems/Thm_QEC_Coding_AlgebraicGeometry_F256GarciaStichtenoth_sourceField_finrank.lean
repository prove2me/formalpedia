-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceField_finrank
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceField_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:57:32.848842+00:00
-- url     : https://prove2.me/theorems/b94744af-57df-48ab-88e9-adc1c06dbf13
-- title:
--   F256 Garcia Stichtenoth: source Field finrank
-- statement:
--   The source-recursion level has degree `16^i` over the initial rational
--   function field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRecursion.lean#L148-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRecursion.lean#L148-L165

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Mathlib.NumberTheory.FunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceField_finrank (i : ℕ) :
    Module.finrank (RatFunc F256) (SourceField i) = 16 ^ i := by sorry
