-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_source_even
-- name    : QEC.Coding.BDL26LocalSearchFailureReduction.source_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:03:55.018176+00:00
-- url     : https://prove2.me/theorems/2bd72934-75ea-408a-9a59-e120c2ea3462
-- title:
--   BDL26 Local Search Failure Reduction: source even
-- statement:
--   Source-even k1/C2 is included in the same necessary-failure statement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LocalSearchFailureReduction.lean#L307-L312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LocalSearchFailureReduction.lean#L307-L312

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_source_even
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_source_even
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_source_even

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalSearchFailureReduction
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators

theorem QEC.Coding.BDL26LocalSearchFailureReduction.source_even (S : OddScale) (k : Nat) (hk : 1 ≤ k)
    (u : XSyndromeDomain S (2*(k-1))) (q : Physical S (2*(k-1)+2))
    (hc : BDL26LogicalDefectProtection.chiX S (2*(k-1)) u q=1) :
    2*(k-1)+2=2*k ∧
      (firstReadout S (2*(k-1)) u≠0 ∨ localSearch S (secondReadout S (2*(k-1)) u q)=none) := by sorry
