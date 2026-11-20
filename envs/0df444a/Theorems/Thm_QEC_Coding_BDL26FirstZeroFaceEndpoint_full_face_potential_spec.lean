-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_full_face_potential_spec
-- name    : QEC.Coding.BDL26FirstZeroFaceEndpoint.full_face_potential_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:42:02.166788+00:00
-- url     : https://prove2.me/theorems/d9a498cb-0a3a-42d4-bc0d-46eaa6712e11
-- title:
--   BDL26 First Zero Face Endpoint: full face potential spec
-- statement:
--   No earlier correction or SECOND correction is erased in the top equation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroFaceEndpoint.lean#L312-L320
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroFaceEndpoint.lean#L312-L320

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
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

theorem QEC.Coding.BDL26FirstZeroFaceEndpoint.full_face_potential_spec (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hs : firstReadout S n u=0) (hf : terminalFace S n u q z f) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (fullFacePotential S n u q z f hf)=
      BDL26LogicalDefectProtection.deltaX S n u q := by sorry
