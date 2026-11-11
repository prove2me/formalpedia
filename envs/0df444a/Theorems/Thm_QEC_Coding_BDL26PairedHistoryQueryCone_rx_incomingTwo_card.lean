-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_rx_incomingTwo_card
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.rx_incomingTwo_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:05:47.258789+00:00
-- url     : https://prove2.me/theorems/314e4977-3638-4903-ae7e-57987f7cf2ec
-- title:
--   BDL26 Paired History Query Cone: rx incoming Two card
-- statement:
--   The BDL26 Paired History Query Cone construction uses the rx incoming Two card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L55-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L55-L58

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.rx_incomingTwo_card (h : i.val % 2 = 0) (v : Owners S depth i) :
    (xiIndexSet (rxData S depth i h).levelGraph.graph v 2).card ≤ 57 := by sorry
