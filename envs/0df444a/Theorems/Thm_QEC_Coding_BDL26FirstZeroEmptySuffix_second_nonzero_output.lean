-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_second_nonzero_output
-- name    : QEC.Coding.BDL26FirstZeroEmptySuffix.second_nonzero_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:36:42.205797+00:00
-- url     : https://prove2.me/theorems/bf65b32a-91e0-419b-857d-397e3278fa0f
-- title:
--   BDL26 First Zero Empty Suffix: second nonzero output
-- statement:
--   Nonzero SECOND input keeps a genuinely nonzero original correction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroEmptySuffix.lean#L109-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroEmptySuffix.lean#L109-L112

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_second_nonzero_output

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

theorem QEC.Coding.BDL26FirstZeroEmptySuffix.second_nonzero_output (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2)
    (hs : firstReadout S 0 u=0) (ht : secondReadout S 0 u q≠0) :
    D S (secondReadout S 0 u q)≠0 := by sorry
