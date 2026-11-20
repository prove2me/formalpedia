-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPrimitiveFailureLocalization_first_zero_failure_package
-- name    : QEC.Coding.BDL26RXPrimitiveFailureLocalization.first_zero_failure_package
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:32:24.61408+00:00
-- url     : https://prove2.me/theorems/89092217-a2fd-40fb-ac3f-da6b2d9f5740
-- title:
--   BDL26 RXPrimitive Failure Localization: first zero failure package
-- statement:
--   Original SECOND failure excludes ALL local owners, independently of the leaf syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean#L200-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean#L200-L213

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPrimitiveFailureLocalization
open MultiscaleDecoder PauliSymplectic BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26OwnerIncidenceMasks
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder BDL26RXPhysicalCoordinateTrace
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXPrimitiveFailureLocalization.first_zero_failure_package (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (hs : firstReadout S N u=0)
    (hc : BDL26LogicalDefectProtection.chiX S N u q=1) :
    (∃ (b : Nat) (hb : b≤N) (p : Primitive S b), parse S N q=.primitive p ∧
      (BDL26BoundaryTailInvariance.snapshot S N u q ⟨b,Nat.lt_succ_of_le hb⟩).word=
        canonicalBasisWord (F:=F) p.physical) ∧
    BDL26LevelTwoLocalBranchEndpoint.localSearch S (secondReadout S N u q)=none ∧
    (¬∃ e : BDL26LevelTwoLocalBranchEndpoint.Error S, levelTwoLocalError S e ∧
      BDL26LevelTwoLocalBranchEndpoint.delta S e=secondReadout S N u q) ∧
    secondReadout S N u q≠0 := by sorry
