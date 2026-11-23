-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_co_perp
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.co_perp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:09.898427+00:00
-- url     : https://prove2.me/theorems/a13f87d3-d49d-41d6-bfd1-fc2aefbc27ba
-- title:
--   Place Perm Operator Bicommutant Span: co perp
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the co perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L178-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L178-L179

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

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.co_perp {L : AddSubgroup V} (hL : CO L) : CO (perpG h L) := by sorry
