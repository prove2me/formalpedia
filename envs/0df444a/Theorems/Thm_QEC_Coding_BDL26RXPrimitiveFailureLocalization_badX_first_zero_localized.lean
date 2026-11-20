-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPrimitiveFailureLocalization_badX_first_zero_localized
-- name    : QEC.Coding.BDL26RXPrimitiveFailureLocalization.badX_first_zero_localized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:27:29.086851+00:00
-- url     : https://prove2.me/theorems/66175f8d-f9f0-4739-99b4-ad3644c35bce
-- title:
--   BDL26 RXPrimitive Failure Localization: bad X first zero localized
-- statement:
--   The BDL26 RXPrimitive Failure Localization construction uses the bad X first zero localized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean#L251-L265
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean#L251-L265

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

theorem QEC.Coding.BDL26RXPrimitiveFailureLocalization.badX_first_zero_localized (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (hu : u∈BDL26LogicalDefectProtection.badX S N) (hs : firstReadout S N u=0) :
    ∃ (q : Physical S (N+2)) (b : Nat) (hb : b≤N) (p : Primitive S b),
      1≤b ∧ ¬b%2=0 ∧
      BDL26LogicalDefectProtection.chiX S N u q=1 ∧ parse S N q=.primitive p ∧
      (BDL26BoundaryTailInvariance.snapshot S N u q ⟨b,Nat.lt_succ_of_le hb⟩).word=
        canonicalBasisWord (F:=F) p.physical := by sorry
