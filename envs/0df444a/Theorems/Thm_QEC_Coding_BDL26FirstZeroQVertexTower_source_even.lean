-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_source_even
-- name    : QEC.Coding.BDL26FirstZeroQVertexTower.source_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:58:44.031756+00:00
-- url     : https://prove2.me/theorems/aec0cc6a-db14-45ed-8693-baf1c14e9014
-- title:
--   BDL26 First Zero QVertex Tower: source even
-- statement:
--   Source-even depth 2k includes the unrestricted C2 base at k=1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroQVertexTower.lean#L419-L423
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/FirstZeroQVertexTower.lean#L419-L423

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_source_even
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_source_even
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_source_even

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstZeroQVertexTower
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators

theorem QEC.Coding.BDL26FirstZeroQVertexTower.source_even (S : OddScale) (k : Nat) (hk : 1≤k)
    (u : XSyndromeDomain S (2*(k-1))) (q : Physical S (2*(k-1)+2))
    (t : Tower S (2*(k-1)) q) (hs : firstReadout S (2*(k-1)) u=0) :
    2*(k-1)+2=2*k ∧ BDL26LogicalDefectProtection.chiX S (2*(k-1)) u q=0 := by sorry
