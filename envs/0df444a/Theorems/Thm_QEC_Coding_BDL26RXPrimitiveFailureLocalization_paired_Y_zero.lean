-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPrimitiveFailureLocalization_paired_Y_zero
-- name    : QEC.Coding.BDL26RXPrimitiveFailureLocalization.paired_Y_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:34:55.512047+00:00
-- url     : https://prove2.me/theorems/3e99d482-094a-482f-94f3-3ebd9a376d28
-- title:
--   BDL26 RXPrimitive Failure Localization: paired Y zero
-- statement:
--   The BDL26 RXPrimitive Failure Localization construction uses the paired Y zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean#L285-L289
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean#L285-L289

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_paired_Y_zero
import Theorems.Thm_QEC_Coding_BDL26HigherRXFaceTower_paired_Y_zero
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_paired_Y_zero
import Theorems.Thm_QEC_Coding_BDL26RZLocalEdgeTower_paired_Y_zero

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPrimitiveFailureLocalization
open MultiscaleDecoder PauliSymplectic BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26OwnerIncidenceMasks
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder BDL26RXPhysicalCoordinateTrace
open scoped Classical BigOperators
open QEC.Semantics BDL26PairedDecoderPhase

theorem QEC.Coding.BDL26RXPrimitiveFailureLocalization.paired_Y_zero (S : OddScale) (N : Nat) (s : Visible S N)
    (q : Physical S (N+2)) (hs : firstReadout S N s.1=0)
    (hSafe : (parse S N q).safe=true) :
    BDL26LogicalDefectProtection.dX S N s (CSSDaviesLocality.singlePauli q .y)=0 := by sorry
