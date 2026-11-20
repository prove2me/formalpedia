-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPrimitiveFailureLocalization_badX_subset_events
-- name    : QEC.Coding.BDL26RXPrimitiveFailureLocalization.badX_subset_events
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:52:58.34568+00:00
-- url     : https://prove2.me/theorems/11277caa-04e8-4d1c-ab2d-d7315b4ad2bf
-- title:
--   BDL26 RXPrimitive Failure Localization: bad X subset events
-- statement:
--   The BDL26 RXPrimitive Failure Localization construction uses the bad X subset events property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean#L267-L275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean#L267-L275

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_badX_subset_events

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

theorem QEC.Coding.BDL26RXPrimitiveFailureLocalization.badX_subset_events (S : OddScale) (N : Nat) :
    BDL26LogicalDefectProtection.badX S N ⊆
      BDL26LocalSearchFailureReduction.firstEvent S N ∪ primitiveEvent S N := by sorry
