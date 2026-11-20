-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_physical_potential_formula
-- name    : QEC.Coding.BDL26BoundaryTailInvariance.physical_potential_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:43:47.851307+00:00
-- url     : https://prove2.me/theorems/0d325428-314f-4002-93a5-63b9ff13b886
-- title:
--   BDL26 Boundary Tail Invariance: physical potential formula
-- statement:
--   The full accumulation is literally the original physical accumulation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundaryTailInvariance.lean#L339-L345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundaryTailInvariance.lean#L339-L345

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

theorem QEC.Coding.BDL26BoundaryTailInvariance.physical_potential_formula (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n u q a).word) :
    physicalPotential S n u q a p hp=
      intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
        (tailPotential S n _ _ (physicalTop S n u q) a p hp 0 (Nat.zero_le _))+
        BDL26ActualFailureReadout.accumulated S n u q := by sorry
