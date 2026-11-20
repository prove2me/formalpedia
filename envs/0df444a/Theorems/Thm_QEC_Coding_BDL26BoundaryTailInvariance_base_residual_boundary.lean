-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_base_residual_boundary
-- name    : QEC.Coding.BDL26BoundaryTailInvariance.base_residual_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:44:04.803863+00:00
-- url     : https://prove2.me/theorems/aa6fc9ec-3fb4-4da0-8aaa-7bb3af49affd
-- title:
--   BDL26 Boundary Tail Invariance: base residual boundary
-- statement:
--   The BDL26 Boundary Tail Invariance construction uses the base residual boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundaryTailInvariance.lean#L252-L269
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundaryTailInvariance.lean#L252-L269

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

theorem QEC.Coding.BDL26BoundaryTailInvariance.base_residual_boundary (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (top : LocalizedWord S n sigma tau (TopIndex n)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(path S n sigma tau top a).word) :
    (SuffixData S n).family.coboundary0 0 (tailPotential S n sigma tau top a p hp 0 (Nat.zero_le _))=
      (path S n sigma tau top 0).word+(actualBase S n).decode (actualInputs S n sigma 0)+
        (actualBase S n).decode (actualInputs S n tau 0) := by sorry
