-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_selectedRationalPlace_evaluate_baseCoordinate
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedRationalPlace_evaluate_baseCoordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:07:54.911206+00:00
-- url     : https://prove2.me/theorems/37d5b802-cfa2-48fb-862d-18b39df4943a
-- title:
--   F256 Garcia Stichtenoth: selected Rational Place evaluate base Coordinate
-- statement:
--   Evaluation of the original rational coordinate remembers the literal
--   initial point along every selected split path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SelectedPlaces.lean#L345-L367
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SelectedPlaces.lean#L345-L367

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Recursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedPlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedRationalPlace_evaluate_baseCoordinate :
    ∀ (i : ℕ) (index : SelectedPlaceIndex i),
      (selectedRationalPlace i index).evaluateRegular
          (baseCoordinate i)
          (selectedRationalPlace_baseCoordinate_regular i index) =
        (selectedPlaceIndexBasePoint i index : F256)
  := by sorry
