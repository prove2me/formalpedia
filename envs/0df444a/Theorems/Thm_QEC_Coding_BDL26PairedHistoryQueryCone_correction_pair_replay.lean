-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_correction_pair_replay
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.correction_pair_replay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:06:09.070973+00:00
-- url     : https://prove2.me/theorems/d8293dbb-c0b0-4b5d-8352-ff5a030c9eb9
-- title:
--   BDL26 Paired History Query Cone: correction pair replay
-- statement:
--   Replay the two component differences, without asserting linearity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/LocalReads.lean#L189-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/LocalReads.lean#L189-L206

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.correction_pair_replay (U : Finset (FamilyZ S depth i.succ))
    (s t s' t' : (indexedFamily S depth).Syndrome i.succ)
    (hs : hammingSupport (s.val+t.val) ⊆ U)
    (hs' : hammingSupport (s'.val+t'.val) ⊆ U)
    (ha : AgreeOn (correctionQueries S depth i U) s.val s'.val)
    (hb : AgreeOn (correctionQueries S depth i U) t.val t'.val) :
    (actualStep S depth i s).correction + (actualStep S depth i t).correction =
      (actualStep S depth i s').correction + (actualStep S depth i t').correction := by sorry
