-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSelectedRationalPlace_evaluate_baseCoordinate
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedRationalPlace_evaluate_baseCoordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:48:23.522005+00:00
-- url     : https://prove2.me/theorems/d853fd1b-97e8-4098-bf40-bac3bed88ee8
-- title:
--   F256 Garcia Stichtenoth: source Selected Rational Place evaluate base Coordinate
-- statement:
--   Evaluation of the original rational coordinate remembers the literal
--   initial point along every selected source path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedPlaces.lean#L345-L371
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedPlaces.lean#L345-L371

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedRationalPlace_evaluate_baseCoordinate :
    ∀ (i : ℕ) (index : SourceSelectedPlaceIndex i),
      (sourceSelectedRationalPlace i index).evaluateRegular
          (sourceBaseCoordinate i)
          (sourceSelectedRationalPlace_baseCoordinate_regular i index) =
        (sourceSelectedPlaceIndexBasePoint i index : F256)
  := by sorry
