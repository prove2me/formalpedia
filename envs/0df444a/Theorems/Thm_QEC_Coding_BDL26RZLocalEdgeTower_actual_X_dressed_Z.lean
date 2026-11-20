-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalEdgeTower_actual_X_dressed_Z
-- name    : QEC.Coding.BDL26RZLocalEdgeTower.actual_X_dressed_Z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:26:21.275171+00:00
-- url     : https://prove2.me/theorems/e7996808-78a3-4242-a6d8-a3d688e74d8b
-- title:
--   BDL26 RZLocal Edge Tower: actual X dressed Z
-- statement:
--   The BDL26 RZLocal Edge Tower construction uses the actual X dressed Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RZLocalEdgeTower.lean#L533-L538
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RZLocalEdgeTower.lean#L533-L538

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_actual_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_actual_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_actual_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_actual_X_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_actual_X_dressed_Z

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

theorem QEC.Coding.BDL26RZLocalEdgeTower.actual_X_dressed_Z (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (t : Killed S n q) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q .x*BDL26PairedDecoderChannel.dressedZ S n-
      BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .x)*atom S n s=0 := by sorry
