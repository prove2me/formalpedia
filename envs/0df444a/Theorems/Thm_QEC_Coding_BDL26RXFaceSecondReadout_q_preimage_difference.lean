-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_q_preimage_difference
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.q_preimage_difference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:06:55.461339+00:00
-- url     : https://prove2.me/theorems/faf23aad-c8ea-4fc6-80cf-72606e26be96
-- title:
--   BDL26 RXFace Second Readout: q preimage difference
-- statement:
--   Original Cq preimages differ by one constant on the actual connected graph.
--   This applies to every preimage, independently of which admissible witness the
--   unchanged Classical.choose selector returns.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L215-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L215-L226

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.q_preimage_difference (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (g h : Word F (QDoubleCylinderVertex P q S))
    (he : wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) g=
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) h) :
    ∀ v, h v+g v=h (0,Sum.inl (Sum.inl ()))+g (0,Sum.inl (Sum.inl ())) := by sorry
