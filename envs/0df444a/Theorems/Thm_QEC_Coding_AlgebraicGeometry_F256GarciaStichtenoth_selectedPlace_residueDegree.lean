-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_selectedPlace_residueDegree
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedPlace_residueDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:15:27.11342+00:00
-- url     : https://prove2.me/theorems/56200aa4-0ab8-4983-9741-8c290bd08664
-- title:
--   F256 Garcia Stichtenoth: selected Place residue Degree
-- statement:
--   Every selected coordinate is a rational global place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Enumeration.lean#L123-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Enumeration.lean#L123-L126

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlaceDegree
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Equiv.Fintype
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Enumeration
set_option autoImplicit false
open Filter
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedPlace_residueDegree (i : ℕ) (j : Fin (selectedLength i)) :
    GlobalPlace.residueDegree (selectedPlace i j) = 1 := by sorry
