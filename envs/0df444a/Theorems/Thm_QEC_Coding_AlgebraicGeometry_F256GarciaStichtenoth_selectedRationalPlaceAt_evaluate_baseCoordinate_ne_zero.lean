-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_selectedRationalPlaceAt_evaluate_baseCoordinate_ne_zero
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedRationalPlaceAt_evaluate_baseCoordinate_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:15:50.62545+00:00
-- url     : https://prove2.me/theorems/ded10d7b-b5a6-4b18-85b7-94bf19b0b122
-- title:
--   F256 Garcia Stichtenoth: selected Rational Place At evaluate base Coordinate ne zero
-- statement:
--   The original rational coordinate has nonzero evaluation at every
--   enumerated selected rational place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Enumeration.lean#L95-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Enumeration.lean#L95-L101

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlaceDegree
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Equiv.Fintype
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Enumeration
set_option autoImplicit false
open Filter
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedRationalPlaceAt_evaluate_baseCoordinate_ne_zero (i : ℕ)
    (j : Fin (selectedLength i)) :
    (selectedRationalPlaceAt i j).evaluateRegular
        (baseCoordinate (i + 2))
        (selectedRationalPlaceAt_baseCoordinate_regular i j) ≠ 0 := by sorry
