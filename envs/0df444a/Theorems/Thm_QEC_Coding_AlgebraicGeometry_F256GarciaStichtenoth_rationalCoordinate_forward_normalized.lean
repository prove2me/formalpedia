-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_rationalCoordinate_forward_normalized
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.rationalCoordinate_forward_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:22:17.972434+00:00
-- url     : https://prove2.me/theorems/ce2607d7-8924-4cb2-ae2e-a3665d5e2a45
-- title:
--   F256 Garcia Stichtenoth: rational Coordinate forward normalized
-- statement:
--   The forward basic projection, in the literal two-coordinate field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalCoordinateCells.lean#L52-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalCoordinateCells.lean#L52-L65

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_CoordinateWindows
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalCoordinateCells
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {E : Type*} [_root_.Field E] [Algebra F256 E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.rationalCoordinate_forward_normalized
    (Q : GlobalPlace F256 E) (x y : E) (hx : Transcendental F256 x)
    [FiniteDimensional F256⟮x⟯ E] [Algebra.IsSeparable F256⟮x⟯ E]
    (h : y ^ 16 + y = sourceStepRhs x) :
    PlaceNormalizedExtension Q F256⟮x⟯ (F256⟮x⟯ ⊔ F256⟮y⟯) := by sorry
