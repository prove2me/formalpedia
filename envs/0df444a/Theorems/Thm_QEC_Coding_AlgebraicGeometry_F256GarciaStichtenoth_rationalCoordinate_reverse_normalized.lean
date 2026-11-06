-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_rationalCoordinate_reverse_normalized
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.rationalCoordinate_reverse_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:22:41.300754+00:00
-- url     : https://prove2.me/theorems/2fe079d1-35cc-43cb-95a9-756d1c90bb54
-- title:
--   F256 Garcia Stichtenoth: rational Coordinate reverse normalized
-- statement:
--   The reverse basic projection is derived from the same displayed
--   equation, then identified with the very same two-coordinate field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalCoordinateCells.lean#L69-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalCoordinateCells.lean#L69-L82

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_CoordinateWindows
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalCoordinateCells
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {E : Type*} [_root_.Field E] [Algebra F256 E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.rationalCoordinate_reverse_normalized
    (Q : GlobalPlace F256 E) (x y : E)
    (hx : Transcendental F256 x) (hy : Transcendental F256 y)
    [FiniteDimensional F256⟮y⟯ E] [Algebra.IsSeparable F256⟮y⟯ E]
    (h : y ^ 16 + y = sourceStepRhs x) :
    PlaceNormalizedExtension Q F256⟮y⟯ (F256⟮x⟯ ⊔ F256⟮y⟯) := by sorry
