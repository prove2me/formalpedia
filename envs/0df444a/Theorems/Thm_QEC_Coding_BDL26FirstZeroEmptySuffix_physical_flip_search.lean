-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_physical_flip_search
-- name    : QEC.Coding.BDL26FirstZeroEmptySuffix.physical_flip_search
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:56:57.966179+00:00
-- url     : https://prove2.me/theorems/ca5b84b3-0166-4ed2-8b60-dcc78b4000af
-- title:
--   BDL26 First Zero Empty Suffix: physical flip search
-- statement:
--   The unchanged first table succeeds on every physical elementary syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroEmptySuffix.lean#L53-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroEmptySuffix.lean#L53-L56

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

theorem QEC.Coding.BDL26FirstZeroEmptySuffix.physical_flip_search (S : OddScale) (q : Physical S 2) :
    BDL26LevelTwoLocalBranchEndpoint.localSuccess S (delta S (flip S 0 q)) := by sorry
