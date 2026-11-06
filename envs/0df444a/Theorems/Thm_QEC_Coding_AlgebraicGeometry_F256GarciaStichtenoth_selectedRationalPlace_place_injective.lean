-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_selectedRationalPlace_place_injective
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedRationalPlace_place_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:06:37.575478+00:00
-- url     : https://prove2.me/theorems/c293f9dd-f223-4874-b01e-2df4f5217f2f
-- title:
--   F256 Garcia Stichtenoth: selected Rational Place place injective
-- statement:
--   Distinct finite paths also have distinct underlying normalized global
--   places.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SelectedPlaces.lean#L260-L266
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SelectedPlaces.lean#L260-L266

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Recursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedPlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedRationalPlace_place_injective (i : ℕ) :
    Function.Injective (fun index : SelectedPlaceIndex i =>
      (selectedRationalPlace i index).place) := by sorry
