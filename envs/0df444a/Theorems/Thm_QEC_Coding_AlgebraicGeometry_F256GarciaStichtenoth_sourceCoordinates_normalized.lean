-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceCoordinates_normalized
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceCoordinates_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:35:29.350445+00:00
-- url     : https://prove2.me/theorems/8252160c-d87b-4102-8998-7257bff030bb
-- title:
--   F256 Garcia Stichtenoth: source Coordinates normalized
-- statement:
--   The original source tower, inside its constructed terminal field,
--   admits the normalized quadratic refinement derived from the paper's
--   coordinate pyramid. Residue finiteness is derived from this function field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceCoordinates.lean#L190-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceCoordinates.lean#L190-L200

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalCoordinateCells
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceCoordinates
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceCoordinates_normalized (m : ℕ) (Q : GlobalPlace F256 (SourceField m)) :
    PlaceNormalizedExtension Q F256⟮sourceCoordinates m 0⟯ ⊤ := by sorry
