-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_gradientInput_x_zero
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.gradientInput_x_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:05:14.830229+00:00
-- url     : https://prove2.me/theorems/4574aa78-fec6-4897-983e-479061c2bb9b
-- title:
--   BDL26 RXFace Second Readout: gradient Input x zero
-- statement:
--   The BDL26 RXFace Second Readout construction uses the gradient Input x zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L619-L625
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L619-L625

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.gradientInput_x_zero (x y : P.X)
    (g : Word F (DoubleCylinderVertex P x witnessScale)) :
    restrictWordLinear (Lx.syndromeRegion y) (gradientInput x g).val=0 := by sorry
