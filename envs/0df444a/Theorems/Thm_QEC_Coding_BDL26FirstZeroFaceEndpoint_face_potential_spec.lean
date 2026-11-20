-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_face_potential_spec
-- name    : QEC.Coding.BDL26FirstZeroFaceEndpoint.face_potential_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:43:27.848242+00:00
-- url     : https://prove2.me/theorems/4067ef4c-5a5c-4f37-a19d-86f88007744c
-- title:
--   BDL26 First Zero Face Endpoint: face potential spec
-- statement:
--   The BDL26 First Zero Face Endpoint construction uses the face potential spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroFaceEndpoint.lean#L181-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroFaceEndpoint.lean#L181-L185

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

theorem QEC.Coding.BDL26FirstZeroFaceEndpoint.face_potential_spec (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) :
    boundary S (facePotential S z f h hh)=h+D S 0+D S (delta S h) := by sorry
