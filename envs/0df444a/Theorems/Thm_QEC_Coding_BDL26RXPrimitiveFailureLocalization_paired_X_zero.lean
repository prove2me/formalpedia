-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPrimitiveFailureLocalization_paired_X_zero
-- name    : QEC.Coding.BDL26RXPrimitiveFailureLocalization.paired_X_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:33:13.395665+00:00
-- url     : https://prove2.me/theorems/fb730a73-6e8b-46f5-a39c-ab6140225e84
-- title:
--   BDL26 RXPrimitive Failure Localization: paired X zero
-- statement:
--   The BDL26 RXPrimitive Failure Localization construction uses the paired X zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean#L279-L283
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean#L279-L283

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_paired_X_zero
import Theorems.Thm_QEC_Coding_BDL26HigherRXFaceTower_paired_X_zero
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_paired_X_zero
import Theorems.Thm_QEC_Coding_BDL26RZLocalEdgeTower_paired_X_zero

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

theorem QEC.Coding.BDL26RXPrimitiveFailureLocalization.paired_X_zero (S : OddScale) (N : Nat) (s : Visible S N)
    (q : Physical S (N+2)) (hs : firstReadout S N s.1=0)
    (hSafe : (parse S N q).safe=true) :
    BDL26LogicalDefectProtection.dX S N s (CSSDaviesLocality.singlePauli q .x)=0 := by sorry
