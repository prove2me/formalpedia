-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_uniform_c2_weight
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.uniform_c2_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:43:06.359744+00:00
-- url     : https://prove2.me/theorems/8c093a49-5eaf-443e-8e96-3401934c179d
-- title:
--   BDL26 Uniform History Obstruction: uniform c2 weight
-- statement:
--   The weight contraction is on the literal C2 readout of the uniform history.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L161-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L161-L167

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformHistoryObstruction.uniform_c2_weight (S : OddScale) (j : Nat) :
    2 ^ (j + 1) * HammingWeight
      (LevelTwoHistory.syndromeReadout (indexedDecoderData S (2 * j + 4))
        (BDL26OwnerIncidenceMasks.actualHistory S (2 * j + 2) (upperSyndrome S j))
        ⟨2, by omega⟩) ≤ HammingWeight (upperSyndrome S j).val := by sorry
