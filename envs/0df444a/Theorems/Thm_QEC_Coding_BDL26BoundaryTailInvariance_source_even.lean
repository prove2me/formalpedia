-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_source_even
-- name    : QEC.Coding.BDL26BoundaryTailInvariance.source_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:36:24.921196+00:00
-- url     : https://prove2.me/theorems/7be5eb6e-fabf-437f-b52e-a17e4889f0c2
-- title:
--   BDL26 Boundary Tail Invariance: source even
-- statement:
--   The BDL26 Boundary Tail Invariance construction uses the source even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundaryTailInvariance.lean#L367-L372
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundaryTailInvariance.lean#L367-L372

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_source_even
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_source_even

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundaryTailInvariance
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26TannerLocalRegularity
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26TransposedStoppedDecoder PauliSymplectic
open scoped Classical

theorem QEC.Coding.BDL26BoundaryTailInvariance.source_even (S : OddScale) (k : Nat) (hk : 1≤k)
    (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S (2*(k-1))) (q : Physical S (2*(k-1)+2))
    (a : LevelIndex (2*(k-1))) (p : V S (2*(k-1)) a)
    (hp : (SuffixData S (2*(k-1))).family.coboundary0 a p=(snapshot S (2*(k-1)) u q a).word) :
    2*(k-1)+2=2*k ∧ BDL26LogicalDefectProtection.chiX S (2*(k-1)) u q=0 := by sorry
