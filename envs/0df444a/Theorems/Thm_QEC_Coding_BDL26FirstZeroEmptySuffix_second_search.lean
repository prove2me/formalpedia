-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_second_search
-- name    : QEC.Coding.BDL26FirstZeroEmptySuffix.second_search
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:15:52.403506+00:00
-- url     : https://prove2.me/theorems/80661c1b-22b5-44b6-9e3e-0b9e7fbd9a5d
-- title:
--   BDL26 First Zero Empty Suffix: second search
-- statement:
--   Actual SECOND search success is derived, never accepted as caller data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroEmptySuffix.lean#L90-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroEmptySuffix.lean#L90-L94

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_second_search

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

theorem QEC.Coding.BDL26FirstZeroEmptySuffix.second_search (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2)
    (hs : firstReadout S 0 u=0) :
    BDL26LevelTwoLocalBranchEndpoint.localSuccess S (secondReadout S 0 u q) := by sorry
