-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceRecursion_equation
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceRecursion_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:55:58.676166+00:00
-- url     : https://prove2.me/theorems/caf0e312-3cf5-44d1-99ab-bce7cd882b13
-- title:
--   F256 Garcia Stichtenoth: source Recursion equation
-- statement:
--   The source recursion equation holds at every actual level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRecursion.lean#L177-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRecursion.lean#L177-L183

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Mathlib.NumberTheory.FunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceRecursion_equation (i : ℕ) :
    sourceDistinguishedCoordinate (i + 1) ^ 16 +
        sourceDistinguishedCoordinate (i + 1) =
      sourceRecursionEmbedding i
        (sourceStepRhs (sourceDistinguishedCoordinate i)) := by sorry
