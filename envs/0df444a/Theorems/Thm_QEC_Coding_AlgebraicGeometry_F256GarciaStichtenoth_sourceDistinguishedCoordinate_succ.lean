-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceDistinguishedCoordinate_succ
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceDistinguishedCoordinate_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:01:07.807619+00:00
-- url     : https://prove2.me/theorems/25e417a5-fb5e-4cca-aa2d-ef2955dc6a66
-- title:
--   F256 Garcia Stichtenoth: source Distinguished Coordinate succ
-- statement:
--   The successor coordinate is the literal coordinate constructed by the
--   one-step source recursion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRecursion.lean#L169-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRecursion.lean#L169-L174

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Mathlib.NumberTheory.FunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceDistinguishedCoordinate_succ (i : ℕ) :
    sourceDistinguishedCoordinate (i + 1) =
      sourceStepCoordinate (sourceDistinguishedPlace i)
        (sourceDistinguishedCoordinate i)
        (sourceDistinguishedCoordinate_order i) := by sorry
