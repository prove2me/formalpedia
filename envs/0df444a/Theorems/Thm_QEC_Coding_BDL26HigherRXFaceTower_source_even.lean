-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HigherRXFaceTower_source_even
-- name    : QEC.Coding.BDL26HigherRXFaceTower.source_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:17:17.313773+00:00
-- url     : https://prove2.me/theorems/55ca8881-073a-4afd-b595-74d020067a7a
-- title:
--   BDL26 Higher RXFace Tower: source even
-- statement:
--   The BDL26 Higher RXFace Tower construction uses the source even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/HigherRXFaceTower.lean#L528-L532
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/HigherRXFaceTower.lean#L528-L532

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_HigherRXFaceTower
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_source_even
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_source_even
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_source_even
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_source_even
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_source_even

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HigherRXFaceTower
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26TransposedStoppedDecoder
open PauliSymplectic
open scoped Classical BigOperators

theorem QEC.Coding.BDL26HigherRXFaceTower.source_even (S : OddScale) (k : Nat) (hk : 1 ≤ k)
    (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S (2*(k-1)))
    (q : Physical S (2*(k-1)+2)) (t : Family S (2*(k-1)) q) :
    2*(k-1)+2=2*k ∧ BDL26LogicalDefectProtection.chiX S (2*(k-1)) u q=0 := by sorry
