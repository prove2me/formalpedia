-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_embeddedSourceCoordinates_units
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.embeddedSourceCoordinates_units
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:34:05.725008+00:00
-- url     : https://prove2.me/theorems/f134c7f8-368c-4ea8-a7ee-79f6a6ed7e6c
-- title:
--   F256 Garcia Stichtenoth: embedded Source Coordinates units
-- statement:
--   The preceding calculation on every coordinate of an actual embedded
--   source field, with its actual image of w as the sole local unit premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRegularCoordinates.lean#L64-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRegularCoordinates.lean#L64-L74

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceCoordinates
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalTraceSeed
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRegularCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {E : Type*} [_root_.Field E] [Algebra F256 E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.embeddedSourceCoordinates_units (m : ℕ) (f : SourceField m →ₐ[F256] E)
    (Q : GlobalPlace F256 E)
    (hw : Q.valuation (f (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)) = 1)
    (i : ℕ) (hi : i ≤ m) :
    Q.valuation (f (sourceCoordinates m i)) = 1 ∧
      Q.valuation (f (sourceCoordinates m i) ^ 15 + 1) = 1 := by sorry
