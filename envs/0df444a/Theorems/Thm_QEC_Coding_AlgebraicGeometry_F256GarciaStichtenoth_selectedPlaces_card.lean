-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_selectedPlaces_card
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedPlaces_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:15:12.532563+00:00
-- url     : https://prove2.me/theorems/c3cf7e76-326e-4816-a9e8-113277b17554
-- title:
--   F256 Garcia Stichtenoth: selected Places card
-- statement:
--   The selected-place Finset has exactly the original-family selected length.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Enumeration.lean#L149-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Enumeration.lean#L149-L153

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlaceDegree
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Equiv.Fintype
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Enumeration
set_option autoImplicit false
open Filter
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedPlaces_card (i : ℕ) :
    (selectedPlaces i).card = selectedLength i := by sorry
