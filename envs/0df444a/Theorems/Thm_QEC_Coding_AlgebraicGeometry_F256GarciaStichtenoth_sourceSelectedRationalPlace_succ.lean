-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSelectedRationalPlace_succ
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedRationalPlace_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:48:19.259845+00:00
-- url     : https://prove2.me/theorems/576479df-f653-43f6-a9e7-e1f56b23b7eb
-- title:
--   F256 Garcia Stichtenoth: source Selected Rational Place succ
-- statement:
--   The selected source place at a successor level is the literal rational
--   upper place chosen by the last path coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedPlaces.lean#L246-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedPlaces.lean#L246-L255

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedRationalPlace_succ (i : ℕ)
    (index : SourceSelectedPlaceIndex i)
    (c : LinearMap.ker f256ArtinSchreier) :
    sourceSelectedRationalPlace (i + 1) (index, c) =
      sourceSplitUpperRationalPlace (sourceSelectedRationalPlace i index)
        (sourceDistinguishedPlace i) (sourceDistinguishedCoordinate i)
        (sourceDistinguishedCoordinate_order i)
        (sourceSelectedRationalPlace_coordinate_regular i index)
        (sourceSelectedPlaceData i index).coordinate_split c := by sorry
