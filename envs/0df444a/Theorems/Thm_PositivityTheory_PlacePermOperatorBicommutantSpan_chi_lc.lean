-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_chi_lc
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.chi_lc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:51:34.524911+00:00
-- url     : https://prove2.me/theorems/61e55155-5492-4aaa-803f-5f65b160eee2
-- title:
--   Place Perm Operator Bicommutant Span: chi lc
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the chi lc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L188-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L188-L191

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

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.chi_lc (a : V) : IsLocallyConstant fun y => χ a y := by sorry
