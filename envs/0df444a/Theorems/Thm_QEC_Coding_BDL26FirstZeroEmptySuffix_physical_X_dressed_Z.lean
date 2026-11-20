-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_physical_X_dressed_Z
-- name    : QEC.Coding.BDL26FirstZeroEmptySuffix.physical_X_dressed_Z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:57:38.589911+00:00
-- url     : https://prove2.me/theorems/9247801d-ec5d-448c-8849-e7cd9b86eeac
-- title:
--   BDL26 First Zero Empty Suffix: physical X dressed Z
-- statement:
--   The BDL26 First Zero Empty Suffix construction uses the physical X dressed Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroEmptySuffix.lean#L192-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroEmptySuffix.lean#L192-L199

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_physical_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_physical_X_dressed_Z

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstZeroEmptySuffix
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
open QEC.Semantics BDL26PairedDecoderPhase

theorem QEC.Coding.BDL26FirstZeroEmptySuffix.physical_X_dressed_Z (S : OddScale) (s : Visible S 0) (q : Physical S 2)
    (hs : firstReadout S 0 s.1=0) :
    (toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x)*BDL26PairedDecoderChannel.dressedZ S 0-
      BDL26PairedDecoderChannel.dressedZ S 0*toHermitianQubitOperator (CSSDaviesLocality.singlePauli q .x))*
      atom S 0 s=0 := by sorry
