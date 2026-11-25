-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_planch
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.planch
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:51:38.930906+00:00
-- url     : https://prove2.me/theorems/8f0006a1-c7b4-44d3-86c9-a6ddedb65302
-- title:
--   Place Perm Operator Bicommutant Span: planch
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the planch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L283-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L283-L305

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
variable [MeasurableSpace V] {χ : V → V → ℂ} {μ : Measure V}
variable (h : NADual V χ μ)
include h

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.planch {φ : V → ℂ} (hφ : SB φ) : ∫ y, ‖fou χ μ φ y‖ ^ 2 ∂μ = ∫ x, ‖φ x‖ ^ 2 ∂μ := by sorry
