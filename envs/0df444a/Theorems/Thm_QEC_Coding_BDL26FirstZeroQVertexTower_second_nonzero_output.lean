-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_second_nonzero_output
-- name    : QEC.Coding.BDL26FirstZeroQVertexTower.second_nonzero_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:30:55.264091+00:00
-- url     : https://prove2.me/theorems/03d6c53a-0363-40f7-8c75-3628056a37e2
-- title:
--   BDL26 First Zero QVertex Tower: second nonzero output
-- statement:
--   The BDL26 First Zero QVertex Tower construction uses the second nonzero output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroQVertexTower.lean#L323-L327
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroQVertexTower.lean#L323-L327

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_second_nonzero_output
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_second_nonzero_output

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstZeroQVertexTower
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators

theorem QEC.Coding.BDL26FirstZeroQVertexTower.second_nonzero_output (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n u=0)
    (ht : secondReadout S n u q≠0) : D S (secondReadout S n u q)≠0 := by sorry
