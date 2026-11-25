-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_fou_ind
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.fou_ind
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:51:20.269592+00:00
-- url     : https://prove2.me/theorems/2b24dfbb-77d4-5a24-a668-f20ece31e619
-- title:
--   Place Perm Operator Bicommutant Span: fou ind
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the fou ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L221-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L221-L253

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

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.fou_ind {L : AddSubgroup V} (hL : CO L) (a y : V) :
    fou χ μ (ind a L) y = ((μ L).toReal : ℂ) * χ a y * ind 0 (perpG h L) y := by sorry
