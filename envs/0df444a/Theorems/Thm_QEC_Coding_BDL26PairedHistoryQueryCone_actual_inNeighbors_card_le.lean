-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_actual_inNeighbors_card_le
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.actual_inNeighbors_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:06:26.604203+00:00
-- url     : https://prove2.me/theorems/714bbf74-ea11-494e-b044-ac7b9e00d709
-- title:
--   BDL26 Paired History Query Cone: actual in Neighbors card le
-- statement:
--   The BDL26 Paired History Query Cone construction uses the actual in Neighbors card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L37-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L37-L53

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.actual_inNeighbors_card_le (h : i.val % 2 = 0) (v : Owners S depth i) :
    (outNeighbors (reverseGraph (rxData S depth i h).levelGraph.graph) v).card ≤ 7 := by sorry
