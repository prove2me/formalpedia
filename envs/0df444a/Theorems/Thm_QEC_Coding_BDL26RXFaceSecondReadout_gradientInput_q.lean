-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_gradientInput_q
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.gradientInput_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:06:16.877241+00:00
-- url     : https://prove2.me/theorems/75272d4a-19d9-4a93-971f-309a49ae1053
-- title:
--   BDL26 RXFace Second Readout: gradient Input q
-- statement:
--   Exact actual cleaned input at every incident Q block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L633-L648
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L633-L648

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.gradientInput_q (x : P.X) (g : Word F (DoubleCylinderVertex P x witnessScale))
    (q : P.Q) (hxq : P.xq x q=true) :
    restrictWordLinear (Lq.syndromeRegion q)
      (RXCoarseGraining.RXCoarseGrainingData.rxSigmaAfterCx Data (gradientInput x g).val)=
      wordEquiv (qSyndromeEquiv P witnessScale q)
        (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale)
          (rxXQDegreeZero P (state witnessScale 2).admissible.toTannerSquareAdmissible
            q x hxq witnessScale g)) := by sorry
