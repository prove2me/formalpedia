-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_zero_x_component_boundary
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.zero_x_component_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:10:01.995059+00:00
-- url     : https://prove2.me/theorems/7bb57d0a-4473-4bfe-88e8-ed3d0bb8466b
-- title:
--   BDL26 RXFace Second Readout: zero x component boundary
-- statement:
--   Zero X input forces zero GLOBAL differential of every original Cx component.
--   The selected correction itself need not vanish.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L461-L488
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L461-L488

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.zero_x_component_boundary (sigma : Syn) (x : P.X)
    (hx : restrictWordLinear (Lx.syndromeRegion x) sigma.val=0) :
    (indexedFamily witnessScale 3).coboundary1 rxIndex.succ
      (RXCoarseGraining.RXCoarseGrainingData.cxComponentTotal Data sigma.val x)=0 := by sorry
