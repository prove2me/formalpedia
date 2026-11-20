-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_physical_potential_spec
-- name    : QEC.Coding.BDL26BoundaryTailInvariance.physical_potential_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:42:04.884695+00:00
-- url     : https://prove2.me/theorems/c3e29cae-1e93-4f6e-bca1-67a702c5dd89
-- title:
--   BDL26 Boundary Tail Invariance: physical potential spec
-- statement:
--   The BDL26 Boundary Tail Invariance construction uses the physical potential spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundaryTailInvariance.lean#L347-L355
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundaryTailInvariance.lean#L347-L355

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
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

theorem QEC.Coding.BDL26BoundaryTailInvariance.physical_potential_spec (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n u q a).word) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (physicalPotential S n u q a p hp)=
      BDL26LogicalDefectProtection.deltaX S n u q := by sorry
