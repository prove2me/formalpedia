-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_selectedQWord_flow_zero
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.selectedQWord_flow_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:09:37.064455+00:00
-- url     : https://prove2.me/theorems/403e73c5-6d70-4f3b-ae0b-fd51b40d51e0
-- title:
--   BDL26 RXFace Second Readout: selected QWord flow zero
-- statement:
--   Every Q block with zero cleaned input has zero ACTUAL outgoing flow.
--   No zero value is assumed for the selected correction word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L508-L522
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L508-L522

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.selectedQWord_flow_zero (sigma : Syn) (q : P.Q)
    (hq : restrictWordLinear (Lq.syndromeRegion q)
      (RXCoarseGraining.RXCoarseGrainingData.rxSigmaAfterCx Data sigma.val)=0) :
    BDL26RXDecoderAdapter.qFlow P witnessScale q (selectedQWord sigma q)=0 := by sorry
