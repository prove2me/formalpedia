-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_actual_Y_package
-- name    : QEC.Coding.BDL26BoundaryTailInvariance.actual_Y_package
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:41:22.081043+00:00
-- url     : https://prove2.me/theorems/dfc742a7-9c48-4a57-b51b-fc7b119aadd1
-- title:
--   BDL26 Boundary Tail Invariance: actual Y package
-- statement:
--   The BDL26 Boundary Tail Invariance construction uses the actual Y package property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundaryTailInvariance.lean#L422-L428
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundaryTailInvariance.lean#L422-L428

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
open QEC.Semantics BDL26PairedDecoderPhase

theorem QEC.Coding.BDL26BoundaryTailInvariance.actual_Y_package (S : OddScale) (n : Nat) (s : Visible S n) (q : Physical S (n+2))
    (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n s.1 q a).word) :
    CSSDaviesLocality.coupling q .y=Complex.I • (Qubit.localX q*Qubit.localZ q) ∧
      (BDL26CSSDaviesLocality.coupling S (n+2) q .y*BDL26PairedDecoderChannel.dressedZ S n-
        BDL26PairedDecoderChannel.dressedZ S n*BDL26CSSDaviesLocality.coupling S (n+2) q .y)*atom S n s=0 := by sorry
