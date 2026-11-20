-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceEdgeTower_first_zero_chiX
-- name    : QEC.Coding.BDL26RXFaceEdgeTower.first_zero_chiX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:07:13.245584+00:00
-- url     : https://prove2.me/theorems/c768bd84-d208-4b0f-95fa-d7615acaceba
-- title:
--   BDL26 RXFace Edge Tower: first zero chi X
-- statement:
--   The BDL26 RXFace Edge Tower construction uses the first zero chi X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceEdgeTower.lean#L555-L562
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceEdgeTower.lean#L555-L562

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_first_zero_chiX
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_first_zero_chiX
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_first_zero_chiX

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

theorem QEC.Coding.BDL26RXFaceEdgeTower.first_zero_chiX (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n u=0) :
    BDL26LogicalDefectProtection.chiX S n u q=0 := by sorry
