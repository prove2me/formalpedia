-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_rationalRecursion_reverse
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.rationalRecursion_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:23:00.619885+00:00
-- url     : https://prove2.me/theorems/1ba4d37c-6a8c-4c01-b92c-e426194d8435
-- title:
--   F256 Garcia Stichtenoth: rational Recursion reverse
-- statement:
--   The inverse-coordinate recursion is an algebraic consequence of the
--   source's displayed equation; it is not a second assumed projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalCoordinateCells.lean#L38-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalCoordinateCells.lean#L38-L49

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_CoordinateWindows
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalCoordinateCells
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {E : Type*} [_root_.Field E] [Algebra F256 E]
omit [Algebra F256 E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.rationalRecursion_reverse {x y : E} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : y ^ 16 + y = sourceStepRhs x) :
    x⁻¹ ^ 16 + x⁻¹ = sourceStepRhs y⁻¹ := by sorry
