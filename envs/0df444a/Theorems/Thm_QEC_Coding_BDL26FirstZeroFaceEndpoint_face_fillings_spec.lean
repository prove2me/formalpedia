-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_face_fillings_spec
-- name    : QEC.Coding.BDL26FirstZeroFaceEndpoint.face_fillings_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:52:01.443124+00:00
-- url     : https://prove2.me/theorems/2d7ad8cf-4c4d-45ba-9fde-f3aacf030ee1
-- title:
--   BDL26 First Zero Face Endpoint: face fillings spec
-- statement:
--   The BDL26 First Zero Face Endpoint construction uses the face fillings spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroFaceEndpoint.lean#L166-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroFaceEndpoint.lean#L166-L174

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

theorem QEC.Coding.BDL26FirstZeroFaceEndpoint.face_fillings_spec (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : faceSupported S z f h) :
    (∀ q v, boundary S (faceQPotential S z f h hh) (.inr ⟨q,v⟩)=
      faceResidual S h (.inr ⟨q,v⟩)) ∧
    (∀ q v, (faceResidual S h+boundary S (faceQPotential S z f h hh)) (.inr ⟨q,v⟩)=0) ∧
    boundary S (faceZPotential S z f h hh)=faceResidual S h+boundary S (faceQPotential S z f h hh) ∧
    boundary S (faceZPotential S z f h hh+faceQPotential S z f h hh)=faceResidual S h := by sorry
