-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPrimitiveFailureLocalization_actual_Y_package
-- name    : QEC.Coding.BDL26RXPrimitiveFailureLocalization.actual_Y_package
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:15:33.569901+00:00
-- url     : https://prove2.me/theorems/3e3f4a96-9ab6-48ec-8771-a130aa2131ce
-- title:
--   BDL26 RXPrimitive Failure Localization: actual Y package
-- statement:
--   The BDL26 RXPrimitive Failure Localization construction uses the actual Y package property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean#L315-L322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean#L315-L322

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_actual_Y_package
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_actual_Y_package
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_actual_Y_package
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_actual_Y_package
import Theorems.Thm_QEC_Coding_BDL26HigherRXFaceTower_actual_Y_package
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_actual_Y_package
import Theorems.Thm_QEC_Coding_BDL26RXFaceEdgeTower_actual_Y_package
import Theorems.Thm_QEC_Coding_BDL26RZLocalEdgeTower_actual_Y_package

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

theorem QEC.Coding.BDL26RXPrimitiveFailureLocalization.actual_Y_package (S : OddScale) (N : Nat) (s : Visible S N)
    (q : Physical S (N+2)) (hs : firstReadout S N s.1=0)
    (hSafe : (parse S N q).safe=true) :
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) ∧
    (BDL26CSSDaviesLocality.coupling S (N+2) q .y*BDL26PairedDecoderChannel.dressedZ S N-
      BDL26PairedDecoderChannel.dressedZ S N*BDL26CSSDaviesLocality.coupling S (N+2) q .y)*
      atom S N s=0 := by sorry
