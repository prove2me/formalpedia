-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_physical_base_calls
-- name    : QEC.Coding.BDL26BoundaryTailInvariance.physical_base_calls
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:42:54.35418+00:00
-- url     : https://prove2.me/theorems/45309f79-399c-4dc3-bb5c-06a532df85a1
-- title:
--   BDL26 Boundary Tail Invariance: physical base calls
-- statement:
--   The BDL26 Boundary Tail Invariance construction uses the physical base calls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundaryTailInvariance.lean#L320-L331
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundaryTailInvariance.lean#L320-L331

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

theorem QEC.Coding.BDL26BoundaryTailInvariance.physical_base_calls (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n u q a).word) :
    firstReadout S n u=secondReadout S n u q ∧
      (actualBase S n).decode (actualInputs S n (input S n u) 0)=
        (actualBase S n).decode (actualInputs S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) 0) ∧
      BDL26LevelTwoDecoder.decode S (firstReadout S n u)=
        BDL26LevelTwoDecoder.decode S (secondReadout S n u q) := by sorry
