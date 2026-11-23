-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_map_sum_sb
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.map_sum_sb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:40:05.420239+00:00
-- url     : https://prove2.me/theorems/bdffe25b-8346-4355-b973-65e60c567b2a
-- title:
--   Place Perm Operator Bicommutant Span: map sum sb
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the map sum sb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L211-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L211-L219

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
omit h [AddCommGroup V] [MeasurableSpace V]

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.map_sum_sb {T : (V → ℂ) → (V → ℂ)} (hadd : ∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ')
    (hsm : ∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ) {α : Type} (s : Finset α) (c : α → ℂ) {f : α → V → ℂ}
    (hf : ∀ a, SB (f a)) : T (∑ a ∈ s, c a • f a) = ∑ a ∈ s, c a • T (f a) := by sorry
