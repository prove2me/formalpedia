-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalEdgeTower_paired_Y_zero
-- name    : QEC.Coding.BDL26RZLocalEdgeTower.paired_Y_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:37:12.615249+00:00
-- url     : https://prove2.me/theorems/17954aa4-b4a1-4926-9b73-1de709a50549
-- title:
--   BDL26 RZLocal Edge Tower: paired Y zero
-- statement:
--   The BDL26 RZLocal Edge Tower construction uses the paired Y zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RZLocalEdgeTower.lean#L511-L515
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RZLocalEdgeTower.lean#L511-L515

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_paired_Y_zero

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
open QEC.Semantics BDL26PairedDecoderPhase

theorem QEC.Coding.BDL26RZLocalEdgeTower.paired_Y_zero (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (t : Killed S n q) :
    BDL26LogicalDefectProtection.dX S n s (CSSDaviesLocality.singlePauli q .y)=0 := by sorry
