-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_second_returned
-- name    : QEC.Coding.BDL26FirstZeroEmptySuffix.second_returned
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:56:19.457193+00:00
-- url     : https://prove2.me/theorems/ea417c3f-1465-4c2e-b5ef-9d4ae129b3f6
-- title:
--   BDL26 First Zero Empty Suffix: second returned
-- statement:
--   The actual original returned word is retained without claiming its owner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroEmptySuffix.lean#L97-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroEmptySuffix.lean#L97-L106

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
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

theorem QEC.Coding.BDL26FirstZeroEmptySuffix.second_returned (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2)
    (hs : firstReadout S 0 u=0) :
    ∃ w : Word F (BDL26LevelTwoDecoder.ExecutableQ S),
      BDL26LevelTwoLocalBranchEndpoint.localSearch S (secondReadout S 0 u q)=some w ∧
      D S (secondReadout S 0 u q)=BDL26LevelTwoDecoder.toActualError S w ∧
      levelTwoLocalError S (D S (secondReadout S 0 u q)) ∧
      delta S (D S (secondReadout S 0 u q))=secondReadout S 0 u q := by sorry
