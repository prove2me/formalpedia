-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_qPortWord_root
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.qPortWord_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:07:02.911613+00:00
-- url     : https://prove2.me/theorems/20cda8f3-6c2a-450d-b2b4-00c32fc89907
-- title:
--   BDL26 RXFace Second Readout: q Port Word root
-- statement:
--   The BDL26 RXFace Second Readout construction uses the q Port Word root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L284-L285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L284-L285

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.qPortWord_root (P : TannerSquarePresentation) (q : P.Q) (b : F) :
    qPortWord P q b (0,Sum.inl (Sum.inl ()))=0 := by sorry

attribute [defeq] QEC.Coding.BDL26RXFaceSecondReadout.qPortWord_root
