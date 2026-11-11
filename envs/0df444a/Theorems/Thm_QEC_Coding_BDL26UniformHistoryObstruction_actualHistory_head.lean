-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_actualHistory_head
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.actualHistory_head
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:40:10.391635+00:00
-- url     : https://prove2.me/theorems/06cd45f1-90d8-42e6-833d-efeda23e7532
-- title:
--   BDL26 Uniform History Obstruction: actual History head
-- statement:
--   The canonical tested output is literally the head of the actual C2-stopped
--   history, for every scale and even physical depth at least four.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWitness.lean#L217-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWitness.lean#L217-L223

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks
open BDL26OwnerParentObstruction BDL26ReplacementSupport BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26XLocalRadialParity BDL26XLocalConnectingWeight
open MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26UniformHistoryObstruction.actualHistory_head (S : OddScale) (j : Nat) :
    ∃ tail, actualHistory S (2 * j + 2) (upperSyndrome S j) =
      CorrectionHistoryEntry.step (Fin.last (2 * j + 1))
        (LevelTwoHistory.suffixOutput (indexedDecoderData S (2 * j + 4))
          (Fin.last (2 * j + 1)) (topOutput S j)) :: tail := by sorry
