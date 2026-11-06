-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceCoordinates_window_eq_top
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceCoordinates_window_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:35:29.276951+00:00
-- url     : https://prove2.me/theorems/8cce368c-1873-472b-a38d-9ea809e256e8
-- title:
--   F256 Garcia Stichtenoth: source Coordinates window eq top
-- statement:
--   The last literal window is the existing `SourceField m`, not a newly
--   postulated carrier or an unnamed function field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceCoordinates.lean#L125-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceCoordinates.lean#L125-L138

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalCoordinateCells
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceCoordinates
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceCoordinates_window_eq_top (m : ℕ) :
    coordinateWindow (sourceCoordinates m) 0 m = ⊤ := by sorry
