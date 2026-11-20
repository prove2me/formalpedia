-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_physical_Y_dressed_Z
-- name    : QEC.Coding.BDL26FirstZeroFaceEndpoint.physical_Y_dressed_Z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:33:15.380176+00:00
-- url     : https://prove2.me/theorems/774529b2-27ea-4b4c-8a4a-a7eda0c21715
-- title:
--   BDL26 First Zero Face Endpoint: physical Y dressed Z
-- statement:
--   The BDL26 First Zero Face Endpoint construction uses the physical Y dressed Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroFaceEndpoint.lean#L383-L391
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroFaceEndpoint.lean#L383-L391

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_physical_Y_dressed_Z

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
open QEC.Semantics BDL26PairedDecoderPhase

theorem QEC.Coding.BDL26FirstZeroFaceEndpoint.physical_Y_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n)
    (q : Physical S (n+2)) (z : (P S).Z) (f : ZDoubleCylinderFace (P S) z S)
    (hs : firstReadout S n s.1=0) (hf : terminalFace S n s.1 q z f) :
    (toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y)*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .y))*
      atom S n s=0 := by sorry
