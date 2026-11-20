-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceEdgeTower_terminal_owner
-- name    : QEC.Coding.BDL26RXFaceEdgeTower.terminal_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:01:01.307657+00:00
-- url     : https://prove2.me/theorems/3227a579-df85-4b4e-9677-2d07599619cd
-- title:
--   BDL26 RXFace Edge Tower: terminal owner
-- statement:
--   Every nonzero terminal coordinate has the actual preceding Z owner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceEdgeTower.lean#L423-L427
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceEdgeTower.lean#L423-L427

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFaceEdgeTower
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXFaceEdgeTower.terminal_owner (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (r : RZQ (RawOne S) S)
    (hr : (descent S n u q).word r≠0) :
    BDL26ReplacementSupport.rzCorrectionOwner (RawOne S) S r=Vertex.z (bottomSeed t).1 := by sorry
