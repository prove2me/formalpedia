-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_uniform_c2_readout_zero
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.uniform_c2_readout_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:42:54.168772+00:00
-- url     : https://prove2.me/theorems/5ec917e7-325a-478e-8443-24acb706acc6
-- title:
--   BDL26 Uniform History Obstruction: uniform c2 readout zero
-- statement:
--   Three or more RX steps force the actual terminal syndrome word to vanish.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L170-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L170-L179

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformHistoryObstruction.uniform_c2_readout_zero (S : OddScale) (j : Nat) (hj : 2 ≤ j) :
    LevelTwoHistory.syndromeReadout (indexedDecoderData S (2 * j + 4))
      (BDL26OwnerIncidenceMasks.actualHistory S (2 * j + 2) (upperSyndrome S j))
      ⟨2, by omega⟩ = 0 := by sorry
