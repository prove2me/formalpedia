-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_incomingTwo_subset
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.incomingTwo_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:06:30.760601+00:00
-- url     : https://prove2.me/theorems/3af4c681-8020-42f2-8264-aa35691c12bf
-- title:
--   BDL26 Paired History Query Cone: incoming Two subset
-- statement:
--   The BDL26 Paired History Query Cone construction uses the incoming Two subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L20-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L20-L28

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.incomingTwo_subset {V : Type} [Fintype V] [DecidableEq V]
    (G : DirectedGraph V) (v : V) :
    xiIndexSet G v 2 ⊆ forwardTwo (reverseGraph G) v := by sorry
