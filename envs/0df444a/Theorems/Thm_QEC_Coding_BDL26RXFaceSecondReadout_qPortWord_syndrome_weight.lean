-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_qPortWord_syndrome_weight
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.qPortWord_syndrome_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:09:11.396868+00:00
-- url     : https://prove2.me/theorems/a86e151f-3f4e-4421-b918-c429bc098842
-- title:
--   BDL26 RXFace Second Readout: q Port Word syndrome weight
-- statement:
--   Each actual cone-to-port pair contributes precisely one input edge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L292-L310
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L292-L310

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.qPortWord_syndrome_weight (P : TannerSquarePresentation) (q : P.Q) (b : F) :
    HammingWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale)
      (qPortWord P q b))=Fintype.card (QStarEdge P q) := by sorry
