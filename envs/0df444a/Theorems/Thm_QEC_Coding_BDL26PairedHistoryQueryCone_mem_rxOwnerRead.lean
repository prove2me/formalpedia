-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_mem_rxOwnerRead
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.mem_rxOwnerRead
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:38:51.4132+00:00
-- url     : https://prove2.me/theorems/0d2a4e17-247b-475b-ba6d-a868209d8409
-- title:
--   BDL26 Paired History Query Cone: mem rx Owner Read
-- statement:
--   The BDL26 Paired History Query Cone construction uses the mem rx Owner Read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/LocalReads.lean#L43-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/LocalReads.lean#L43-L56

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_LocalReads
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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.mem_rxOwnerRead (h : i.val % 2 = 0) (v : Owners S depth i)
    (p : FamilyZ S depth i.succ) :
    p ∈ rxOwnerRead S depth i h v ↔
      (rxData S depth i h).levelGraph.graph.distance
        ((rxData S depth i h).topCenter p) v ≤ 2 := by sorry
