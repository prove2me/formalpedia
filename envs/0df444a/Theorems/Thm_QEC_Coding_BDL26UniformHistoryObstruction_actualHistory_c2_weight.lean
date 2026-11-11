-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_actualHistory_c2_weight
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.actualHistory_c2_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:42:27.941196+00:00
-- url     : https://prove2.me/theorems/0db90810-3cbe-40df-8f2a-ffa8dd6dd669
-- title:
--   BDL26 Uniform History Obstruction: actual History c2 weight
-- statement:
--   Actual canonical selectors discharge every primitive alternating inequality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L131-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L131-L158

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformHistoryObstruction.actualHistory_c2_weight (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome (TopIndex (n + 2))) :
    2 ^ ((n + 1) / 2) * HammingWeight
      (LevelTwoHistory.syndromeReadout (indexedDecoderData S (n + 2))
        (BDL26OwnerIncidenceMasks.actualHistory S n sigma) ⟨2, by omega⟩) ≤
      HammingWeight sigma.val := by sorry
