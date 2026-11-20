-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_split_coarse_eq_root_syndrome
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.split_coarse_eq_root_syndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:10:41.972478+00:00
-- url     : https://prove2.me/theorems/ed4962c2-5dbd-4c39-8b58-060472320efa
-- title:
--   BDL26 RXFace Second Readout: split coarse eq root syndrome
-- statement:
--   The complete actual coarse output is the syndrome of the derived root
--   word. The prescribed Z bits cancel by the original Tanner coboundary-square
--   identity, not by summing the two physical output copies.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L770-L784
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L770-L784

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.split_coarse_eq_root_syndrome (x : P.X) :
    (BDL26RXDecoderAdapter.rxStepOutput witnessScale 3 rxIndex rxIndex_even
      (gradientInput x (splitPotential x))).coarse.val=tannerCoboundary1 P (rootWord x) := by sorry
