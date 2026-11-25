-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_meas_perp
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.meas_perp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:51:32.025233+00:00
-- url     : https://prove2.me/theorems/2adae7cd-292e-56bd-8e86-e6f2acb27e7a
-- title:
--   Place Perm Operator Bicommutant Span: meas perp
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the meas perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L184-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L184-L186

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

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.meas_perp {L : AddSubgroup V} (hL : CO L) : (μ L).toReal * (μ (perpG h L)).toReal = 1 := by sorry
