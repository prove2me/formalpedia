-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceEdgeTower_physical_Y_iXZ
-- name    : QEC.Coding.BDL26RXFaceEdgeTower.physical_Y_iXZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:19:36.77117+00:00
-- url     : https://prove2.me/theorems/ecc554e6-5002-4c01-83b3-d040e116b4bc
-- title:
--   BDL26 RXFace Edge Tower: physical Y i XZ
-- statement:
--   The BDL26 RXFace Edge Tower construction uses the physical Y i XZ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceEdgeTower.lean#L573-L575
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceEdgeTower.lean#L573-L575

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_physical_Y_iXZ
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_physical_Y_iXZ
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_physical_Y_iXZ
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_physical_Y_iXZ

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
open QEC.Semantics BDL26PairedDecoderPhase

theorem QEC.Coding.BDL26RXFaceEdgeTower.physical_Y_iXZ (S : OddScale) (n : Nat) (q : Physical S (n+2)) :
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) := by sorry
