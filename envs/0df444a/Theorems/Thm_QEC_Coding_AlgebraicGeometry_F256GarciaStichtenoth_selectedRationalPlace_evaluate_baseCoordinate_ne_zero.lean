-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_selectedRationalPlace_evaluate_baseCoordinate_ne_zero
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedRationalPlace_evaluate_baseCoordinate_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:06:42.523502+00:00
-- url     : https://prove2.me/theorems/ff799ed5-a60d-4c81-8743-288de149f956
-- title:
--   F256 Garcia Stichtenoth: selected Rational Place evaluate base Coordinate ne zero
-- statement:
--   The original rational coordinate has nonzero residue at every selected
--   split place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SelectedPlaces.lean#L307-L341
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SelectedPlaces.lean#L307-L341

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Recursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedPlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedRationalPlace_evaluate_baseCoordinate_ne_zero :
    ∀ (i : ℕ) (index : SelectedPlaceIndex i),
      (selectedRationalPlace i index).evaluateRegular
          (baseCoordinate i)
          (selectedRationalPlace_baseCoordinate_regular i index) ≠ 0
  := by sorry
