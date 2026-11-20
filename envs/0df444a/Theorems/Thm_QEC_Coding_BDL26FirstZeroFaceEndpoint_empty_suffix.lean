-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_empty_suffix
-- name    : QEC.Coding.BDL26FirstZeroFaceEndpoint.empty_suffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:55:15.46092+00:00
-- url     : https://prove2.me/theorems/c068f8b8-37f1-4864-8e79-22ff0f652023
-- title:
--   BDL26 First Zero Face Endpoint: empty suffix
-- statement:
--   The empty interval keeps the same physical flip and has no earlier terms.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroFaceEndpoint.lean#L344-L350
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroFaceEndpoint.lean#L344-L350

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_empty_suffix

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstZeroFaceEndpoint
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators

theorem QEC.Coding.BDL26FirstZeroFaceEndpoint.empty_suffix (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2)
    (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hs : firstReadout S 0 u=0) (hf : terminalFace S 0 u q z f) :
    (descent S 0 u q).word=flip S 0 q ∧ accumulated S 0 u q=0 ∧
      BDL26LogicalDefectProtection.chiX S 0 u q=0 := by sorry
