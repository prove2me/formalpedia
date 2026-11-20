-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceEdgeTower_face_blocks
-- name    : QEC.Coding.BDL26RXFaceEdgeTower.face_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:59:02.146034+00:00
-- url     : https://prove2.me/theorems/104aaf3a-cb86-4bc2-ad16-9b9c346c9ca3
-- title:
--   BDL26 RXFace Edge Tower: face blocks
-- statement:
--   Literal face constructor table, retaining both the empty Q0 and singleton Z0.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceEdgeTower.lean#L119-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceEdgeTower.lean#L119-L124

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

theorem QEC.Coding.BDL26RXFaceEdgeTower.face_blocks (S : OddScale) (z : (RawOne S).Z)
    (f : ZDoubleCylinderFace (RawOne S) z S) :
    BDL26RZPhysicalXStarTransport.Q0 S 2 ⟨1,by omega⟩ (by decide) (faceOwner S z f)=∅ ∧
    BDL26RZPhysicalXStarTransport.Z0 S 2 ⟨1,by omega⟩ (by decide) (faceOwner S z f)={z} := by sorry
