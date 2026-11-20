-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalEdgeTower_second_zero
-- name    : QEC.Coding.BDL26RZLocalEdgeTower.second_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:15:29.364985+00:00
-- url     : https://prove2.me/theorems/dc7f6a24-17e7-4f52-b9c1-d01c077976e7
-- title:
--   BDL26 RZLocal Edge Tower: second zero
-- statement:
--   FIRST-zero is optional; SECOND-zero is a conclusion, never a premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RZLocalEdgeTower.lean#L433-L436
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RZLocalEdgeTower.lean#L433-L436

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

theorem QEC.Coding.BDL26RZLocalEdgeTower.second_zero (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) (hs : firstReadout S n u=0) :
    secondReadout S n u q=0 := by sorry
