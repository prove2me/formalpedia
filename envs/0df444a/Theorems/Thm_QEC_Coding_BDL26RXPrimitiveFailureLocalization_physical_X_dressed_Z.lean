-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPrimitiveFailureLocalization_physical_X_dressed_Z
-- name    : QEC.Coding.BDL26RXPrimitiveFailureLocalization.physical_X_dressed_Z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:48:32.228069+00:00
-- url     : https://prove2.me/theorems/9b9d5ce2-0773-4d28-bf1b-1531efb2f811
-- title:
--   BDL26 RXPrimitive Failure Localization: physical X dressed Z
-- statement:
--   The BDL26 RXPrimitive Failure Localization construction uses the physical X dressed Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean#L291-L297
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean#L291-L297

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_physical_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_physical_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_physical_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_physical_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_physical_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26HigherRXFaceTower_physical_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_physical_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26RXFaceEdgeTower_physical_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26RZLocalEdgeTower_physical_X_dressed_Z

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

theorem QEC.Coding.BDL26RXPrimitiveFailureLocalization.physical_X_dressed_Z (S : OddScale) (N : Nat) (s : Visible S N)
    (q : Physical S (N+2)) (hs : firstReadout S N s.1=0)
    (hSafe : (parse S N q).safe=true) :
    (toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x)*BDL26PairedDecoderChannel.dressedZ S N-
      BDL26PairedDecoderChannel.dressedZ S N*toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x))*
      atom S N s=0 := by sorry
