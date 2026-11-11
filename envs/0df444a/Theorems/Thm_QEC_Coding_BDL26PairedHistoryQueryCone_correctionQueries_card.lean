-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_correctionQueries_card
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.correctionQueries_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:41:04.605149+00:00
-- url     : https://prove2.me/theorems/74142d88-8603-4b2c-bf02-4b4f79e5073a
-- title:
--   BDL26 Paired History Query Cone: correction Queries card
-- statement:
--   The BDL26 Paired History Query Cone construction uses the correction Queries card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L186-L190
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L186-L190

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_LocalReads
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26RXCoarseInfluence
open BDL26RXInfluenceBounds BDL26GraphQuantitativeBounds
open MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26PairedHistoryQueryCone.correctionQueries_card (U : Finset (FamilyZ S depth i.succ)) :
    (correctionQueries S depth i U).card ≤ queryBlockBound S * (57 * U.card) := by sorry
