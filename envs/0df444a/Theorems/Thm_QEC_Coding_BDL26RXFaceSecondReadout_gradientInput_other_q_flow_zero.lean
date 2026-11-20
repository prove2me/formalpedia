-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_gradientInput_other_q_flow_zero
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.gradientInput_other_q_flow_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:03:53.050859+00:00
-- url     : https://prove2.me/theorems/cec443a5-c680-4db3-bda4-593238daf68e
-- title:
--   BDL26 RXFace Second Readout: gradient Input other q flow zero
-- statement:
--   All off-face Q components have zero outgoing flow by the actual budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L651-L661
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L651-L661

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.gradientInput_other_q_flow_zero (x : P.X)
    (g : Word F (DoubleCylinderVertex P x witnessScale)) (q : P.Q)
    (hxq : P.xq x q≠true) :
    qFlow P witnessScale q (selectedQWord (gradientInput x g) q)=0 := by sorry
