-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_selectedQWord_forced
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.selectedQWord_forced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:09:49.254181+00:00
-- url     : https://prove2.me/theorems/1723a591-aba6-481b-893a-60633421444e
-- title:
--   BDL26 RXFace Second Readout: selected QWord forced
-- statement:
--   Actual selected-word forcing. The sole hypothesis specifies the computed
--   cleaned input; both its range and the unchanged selector's budget are derived
--   here, rather than supplied as a selected correction certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L436-L454
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L436-L454

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.selectedQWord_forced (sigma : Syn) (q : P.Q) (b : F)
    (hinput : restrictWordLinear (Lq.syndromeRegion q)
      (RXCoarseGraining.RXCoarseGrainingData.rxSigmaAfterCx Data sigma.val)=
      wordEquiv (BDL26RXDecoderAdapter.qSyndromeEquiv P witnessScale q)
        (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale)
          (qPortWord P q b))) :
    selectedQWord sigma q (0,Sum.inl (Sum.inl ()))=b := by sorry
