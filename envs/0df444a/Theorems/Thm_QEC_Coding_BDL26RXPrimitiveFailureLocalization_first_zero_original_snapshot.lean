-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPrimitiveFailureLocalization_first_zero_original_snapshot
-- name    : QEC.Coding.BDL26RXPrimitiveFailureLocalization.first_zero_original_snapshot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:32:10.276475+00:00
-- url     : https://prove2.me/theorems/f93c363a-915c-4592-ad04-9126baf43ef7
-- title:
--   BDL26 RXPrimitive Failure Localization: first zero original snapshot
-- statement:
--   The stored snapshot is the existing actualDescent with the original top input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean#L187-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean#L187-L197

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

theorem QEC.Coding.BDL26RXPrimitiveFailureLocalization.first_zero_original_snapshot (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (hs : firstReadout S N u=0)
    (hc : BDL26LogicalDefectProtection.chiX S N u q=1) :
    ∃ (b : Nat) (hb : b≤N) (p : Primitive S b), parse S N q=.primitive p ∧
      (actualDescent S N (input S N u) (flip S N q) (elementaryCenter S N q)
        (BDL26BoundaryTailInvariance.physical_supported S N q) ⟨b,Nat.lt_succ_of_le hb⟩).word=
          canonicalBasisWord (F:=F) p.physical := by sorry
