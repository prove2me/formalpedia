-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_full_port_weight
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.full_port_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:08:25.991566+00:00
-- url     : https://prove2.me/theorems/4083ec71-5625-4532-b363-9c46b578c201
-- title:
--   BDL26 RXFace Second Readout: full port weight
-- statement:
--   The actual outgoing flow counts both copies of every incident Z port.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L314-L328
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L314-L328

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.full_port_weight (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (h : Word F (QDoubleCylinderVertex P q S))
    (hleaf : ∀ (z : QStarEdge P q) (c : BDL26FiniteTannerSquare.Two),
      h (c,Sum.inl (Sum.inr z))=1) :
    HammingWeight (BDL26RXDecoderAdapter.qFlow P S q h)=
      2*Fintype.card (QStarEdge P q) := by sorry
