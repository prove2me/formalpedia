-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_actual_Y_package
-- name    : QEC.Coding.BDL26FirstZeroEmptySuffix.actual_Y_package
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:20:22.725453+00:00
-- url     : https://prove2.me/theorems/51b252fe-b411-4724-8440-c062c0220a51
-- title:
--   BDL26 First Zero Empty Suffix: actual Y package
-- statement:
--   The BDL26 First Zero Empty Suffix construction uses the actual Y package property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroEmptySuffix.lean#L222-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroEmptySuffix.lean#L222-L227

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_actual_Y_package

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

theorem QEC.Coding.BDL26FirstZeroEmptySuffix.actual_Y_package (S : OddScale) (s : Visible S 0) (q : Physical S 2)
    (hs : firstReadout S 0 s.1=0) :
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) ∧
    (BDL26CSSDaviesLocality.coupling S 2 q .y*BDL26PairedDecoderChannel.dressedZ S 0-
      BDL26PairedDecoderChannel.dressedZ S 0*BDL26CSSDaviesLocality.coupling S 2 q .y)*atom S 0 s=0 := by sorry
