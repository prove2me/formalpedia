-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_selectedRationalPlace_coordinate_evaluate_ne_zero
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedRationalPlace_coordinate_evaluate_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:07:33.932729+00:00
-- url     : https://prove2.me/theorems/81d5691f-0621-4560-b634-d39037808736
-- title:
--   F256 Garcia Stichtenoth: selected Rational Place coordinate evaluate ne zero
-- statement:
--   The distinguished coordinate has nonzero residue at every selected
--   place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SelectedPlaces.lean#L224-L229
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SelectedPlaces.lean#L224-L229

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Recursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedPlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedRationalPlace_coordinate_evaluate_ne_zero (i : ℕ)
    (index : SelectedPlaceIndex i) :
    (selectedRationalPlace i index).evaluateRegular
        (distinguishedCoordinate i)
        (selectedRationalPlace_coordinate_regular i index) ≠ 0 := by sorry
