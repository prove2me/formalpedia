-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_selectedQWord_delta
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.selectedQWord_delta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:08:20.93242+00:00
-- url     : https://prove2.me/theorems/daaedeba-d412-4d6b-ad26-440308fda72c
-- title:
--   BDL26 RXFace Second Readout: selected QWord delta
-- statement:
--   Reindexing of the original selected Q equation for any actual cleaned
--   local graph input, including the mixed-port cases with multiple budget choices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L677-L686
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L677-L686

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFaceSecondReadout
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26RXDecoderAdapter
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXFaceSecondReadout.selectedQWord_delta (sigma : Syn) (q : P.Q)
    (g : Word F (QDoubleCylinderVertex P q witnessScale))
    (hinput : restrictWordLinear (Lq.syndromeRegion q)
      (RXCoarseGraining.RXCoarseGrainingData.rxSigmaAfterCx Data sigma.val)=
      wordEquiv (qSyndromeEquiv P witnessScale q)
        (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale) g)) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale)
      (selectedQWord sigma q)=
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale) g := by sorry
