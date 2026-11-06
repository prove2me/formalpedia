-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coordinate_adjoin_inv
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coordinate_adjoin_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:22:07.935149+00:00
-- url     : https://prove2.me/theorems/85f3914a-01a8-4b2f-a912-56a2ed5d5926
-- title:
--   F256 Garcia Stichtenoth: coordinate adjoin inv
-- statement:
--   The F256 Garcia Stichtenoth construction uses the coordinate adjoin inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalCoordinateCells.lean#L20-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalCoordinateCells.lean#L20-L33

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_CoordinateWindows
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalCoordinateCells
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {E : Type*} [_root_.Field E] [Algebra F256 E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coordinate_adjoin_inv (x : E) : F256⟮x⁻¹⟯ = F256⟮x⟯ := by sorry
