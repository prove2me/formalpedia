-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSelectedPlaceIndex_card
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedPlaceIndex_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:46:55.113073+00:00
-- url     : https://prove2.me/theorems/3c11c76c-ccb3-4124-a445-87aead550332
-- title:
--   F256 Garcia Stichtenoth: source Selected Place Index card
-- statement:
--   The selected source path set has exact cardinality `240 * 16^i`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedPlaces.lean#L161-L171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedPlaces.lean#L161-L171

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedPlaceIndex_card (i : ℕ) :
    Fintype.card (SourceSelectedPlaceIndex i) = 240 * 16 ^ i := by sorry
