-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_selectedQWord_boundary_old_z
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.selectedQWord_boundary_old_z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:08:07.162535+00:00
-- url     : https://prove2.me/theorems/7b6cea57-2147-469e-8837-25b333917e09
-- title:
--   BDL26 RXFace Second Readout: selected QWord boundary old z
-- statement:
--   At an original doubled-Z coordinate the complete selected Cq component
--   has exactly its outgoing flow. All auxiliary local-syndrome terms are zero
--   there by their actual constructor, not dropped by an external certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L527-L547
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L527-L547

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.selectedQWord_boundary_old_z (sigma : Syn) (q : P.Q) (z : P.Z) (c : BDL26FiniteTannerSquare.Two) :
    (indexedFamily witnessScale 3).coboundary1 rxIndex.succ
      (RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal Data sigma.val q) (Sum.inr (z,c))=
      BDL26RXDecoderAdapter.qFlow P witnessScale q (selectedQWord sigma q)
        (Sum.inr (z,c)) := by sorry
