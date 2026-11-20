-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_zero_x_cleaned_input
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.zero_x_cleaned_input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:08:57.609527+00:00
-- url     : https://prove2.me/theorems/2fb44978-937f-4899-9624-21f723fc6a42
-- title:
--   BDL26 RXFace Second Readout: zero x cleaned input
-- statement:
--   Every original Cx component remains present. Its global cocycle equation,
--   derived above from the original budget, proves the cleaned Q input is unchanged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L492-L503
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L492-L503

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.zero_x_cleaned_input (sigma : Syn)
    (hx : ∀ x, restrictWordLinear (Lx.syndromeRegion x) sigma.val=0) :
    RXCoarseGraining.RXCoarseGrainingData.rxSigmaAfterCx Data sigma.val=sigma.val := by sorry
