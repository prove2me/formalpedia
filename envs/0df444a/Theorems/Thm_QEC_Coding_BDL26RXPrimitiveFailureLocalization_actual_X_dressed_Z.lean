-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPrimitiveFailureLocalization_actual_X_dressed_Z
-- name    : QEC.Coding.BDL26RXPrimitiveFailureLocalization.actual_X_dressed_Z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:01:00.446039+00:00
-- url     : https://prove2.me/theorems/91b6b5c6-552d-4d58-9657-370fde9ece64
-- title:
--   BDL26 RXPrimitive Failure Localization: actual X dressed Z
-- statement:
--   The BDL26 RXPrimitive Failure Localization construction uses the actual X dressed Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean#L307-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean#L307-L313

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_actual_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_actual_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_actual_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_actual_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_actual_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26HigherRXFaceTower_actual_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_actual_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26RXFaceEdgeTower_actual_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26RZLocalEdgeTower_actual_X_dressed_Z

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

theorem QEC.Coding.BDL26RXPrimitiveFailureLocalization.actual_X_dressed_Z (S : OddScale) (N : Nat) (s : Visible S N)
    (q : Physical S (N+2)) (hs : firstReadout S N s.1=0)
    (hSafe : (parse S N q).safe=true) :
    (BDL26CSSDaviesLocality.coupling S (N+2) q .x*BDL26PairedDecoderChannel.dressedZ S N-
      BDL26PairedDecoderChannel.dressedZ S N*BDL26CSSDaviesLocality.coupling S (N+2) q .x)*
      atom S N s=0 := by sorry
