-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_selectedPlaceIndex_card
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedPlaceIndex_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:07:30.394948+00:00
-- url     : https://prove2.me/theorems/e6c70ae9-c53f-4030-82dd-7ed4c8ae4ab6
-- title:
--   F256 Garcia Stichtenoth: selected Place Index card
-- statement:
--   The selected-place index set has the exact source-facing cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SelectedPlaces.lean#L148-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SelectedPlaces.lean#L148-L157

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Recursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedPlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedPlaceIndex_card (i : ℕ) :
    Fintype.card (SelectedPlaceIndex i) = 255 * 16 ^ i := by sorry
