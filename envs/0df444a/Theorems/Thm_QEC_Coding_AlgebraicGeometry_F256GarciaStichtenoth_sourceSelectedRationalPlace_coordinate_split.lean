-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSelectedRationalPlace_coordinate_split
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedRationalPlace_coordinate_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:47:07.341517+00:00
-- url     : https://prove2.me/theorems/013ca494-3ac7-4217-96bb-0570cdcc4762
-- title:
--   F256 Garcia Stichtenoth: source Selected Rational Place coordinate split
-- statement:
--   The source coordinate retains the exact split condition at every selected
--   place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedPlaces.lean#L259-L265
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedPlaces.lean#L259-L265

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedRationalPlace_coordinate_split (i : ℕ)
    (index : SourceSelectedPlaceIndex i) :
    galoisBaseWValue
        ((sourceSelectedRationalPlace i index).evaluateRegular
          (sourceDistinguishedCoordinate i)
          (sourceSelectedRationalPlace_coordinate_regular i index)) ≠ 0 := by sorry
