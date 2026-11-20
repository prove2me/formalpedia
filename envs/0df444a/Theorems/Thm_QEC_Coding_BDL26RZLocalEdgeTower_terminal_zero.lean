-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalEdgeTower_terminal_zero
-- name    : QEC.Coding.BDL26RZLocalEdgeTower.terminal_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:15:11.778267+00:00
-- url     : https://prove2.me/theorems/217b342d-5aef-47d6-a4a7-e16ab85fbd8e
-- title:
--   BDL26 RZLocal Edge Tower: terminal zero
-- statement:
--   The BDL26 RZLocal Edge Tower construction uses the terminal zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RZLocalEdgeTower.lean#L378-L382
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RZLocalEdgeTower.lean#L378-L382

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZLocalEdgeTower
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26TransposedStoppedDecoder
open PauliSymplectic
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RZLocalEdgeTower.terminal_zero (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) : (descent S n u q).word=0 := by sorry
