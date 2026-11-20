-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalEdgeTower_step_zero
-- name    : QEC.Coding.BDL26RZLocalEdgeTower.step_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:14:47.608979+00:00
-- url     : https://prove2.me/theorems/72dc7d58-69a2-457a-ba03-362810eb0033
-- title:
--   BDL26 RZLocal Edge Tower: step zero
-- statement:
--   Original zero absorption; RZ Phi is retained and need not be zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RZLocalEdgeTower.lean#L330-L345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RZLocalEdgeTower.lean#L330-L345

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

theorem QEC.Coding.BDL26RZLocalEdgeTower.step_zero (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (i : StepIndex n) (w : LocalizedWord S n sigma tau i.succ) (hw : w.word=0) :
    (step S n sigma tau i w).lower.word=0 := by sorry
