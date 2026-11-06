-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisBaseParameter_evaluate
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisBaseParameter_evaluate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:48:29.015303+00:00
-- url     : https://prove2.me/theorems/f363ff80-301c-4839-893c-05ea0152d390
-- title:
--   F256 Garcia Stichtenoth: source Galois Base Parameter evaluate
-- statement:
--   Every selected source place has the literal residue value `z = 1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedPlaces.lean#L401-L430
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedPlaces.lean#L401-L430

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisBaseParameter_evaluate (i : ℕ)
    (index : SourceSelectedPlaceIndex i) :
    (sourceSelectedRationalPlace i index).evaluateRegular
        (sourceGaloisBaseParameter i)
        (sourceGaloisBaseParameter_regular i index) = 1 := by sorry
