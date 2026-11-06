-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_selectedRationalPlace_succ
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedRationalPlace_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:07:25.608201+00:00
-- url     : https://prove2.me/theorems/4bf7fa14-51b5-4e1f-affd-6fe703507b1c
-- title:
--   F256 Garcia Stichtenoth: selected Rational Place succ
-- statement:
--   The selected place at a successor level is the literal split upper place
--   chosen by the last path coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SelectedPlaces.lean#L212-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SelectedPlaces.lean#L212-L220

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Recursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedPlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedRationalPlace_succ (i : ℕ)
    (index : SelectedPlaceIndex i)
    (c : LinearMap.ker f256ArtinSchreier) :
    selectedRationalPlace (i + 1) (index, c) =
      splitUpperRationalPlace (selectedRationalPlace i index)
        (distinguishedPlace i) (distinguishedCoordinate i)
        (distinguishedCoordinate_order i)
        (selectedRationalPlace_coordinate_regular i index) c := by sorry
