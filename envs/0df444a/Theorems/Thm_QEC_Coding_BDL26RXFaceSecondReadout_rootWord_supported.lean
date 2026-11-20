-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_rootWord_supported
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.rootWord_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:09:42.834303+00:00
-- url     : https://prove2.me/theorems/d54acaa6-1a66-4a0d-8455-e4f2706854c9
-- title:
--   BDL26 RXFace Second Readout: root Word supported
-- statement:
--   The internally constructed root word has exact original face-star support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L740-L743
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L740-L743

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.rootWord_supported (x : P.X) :
    hammingSupport (rootWord x)⊆BDL26RXPhysicalStarTransport.physicalXStar P x := by sorry
