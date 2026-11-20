-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalEdgeTower_source_even
-- name    : QEC.Coding.BDL26RZLocalEdgeTower.source_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:16:38.120787+00:00
-- url     : https://prove2.me/theorems/d34cd88c-2655-4a07-aaea-f6452727406c
-- title:
--   BDL26 RZLocal Edge Tower: source even
-- statement:
--   The BDL26 RZLocal Edge Tower construction uses the source even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RZLocalEdgeTower.lean#L497-L501
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RZLocalEdgeTower.lean#L497-L501

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_source_even
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_source_even
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_source_even
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_source_even
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_source_even

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

theorem QEC.Coding.BDL26RZLocalEdgeTower.source_even (S : OddScale) (k : Nat) (hk : 2 ≤ k)
    (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S (2*(k-1))) (q : Physical S (2*(k-1)+2))
    (t : Killed S (2*(k-1)) q) :
    2*(k-1)+2=2*k ∧ BDL26LogicalDefectProtection.chiX S (2*(k-1)) u q=0 := by sorry
