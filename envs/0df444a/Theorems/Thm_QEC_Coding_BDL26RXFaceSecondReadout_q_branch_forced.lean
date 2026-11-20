-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_q_branch_forced
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.q_branch_forced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:09:26.966429+00:00
-- url     : https://prove2.me/theorems/0af08a18-0283-4627-a4f1-8b3aa693a462
-- title:
--   BDL26 RXFace Second Readout: q branch forced
-- statement:
--   A budget forces the cone-root branch when both actual Z endpoints carry
--   one common bit. It quantifies over EVERY admissible original local preimage;
--   Classical.choose is not replaced, and mixed-endpoint ties are not resolved.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L333-L358
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L333-L358

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.q_branch_forced (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (b : F) (h : Word F (QDoubleCylinderVertex P q witnessScale))
    (hdelta : wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale) h=
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale)
        (qPortWord P q b))
    (hbudget : HammingWeight (BDL26RXDecoderAdapter.qFlow P witnessScale q h) ≤
      HammingWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q witnessScale)
        (qPortWord P q b))) :
    h (0,Sum.inl (Sum.inl ()))=b := by sorry
