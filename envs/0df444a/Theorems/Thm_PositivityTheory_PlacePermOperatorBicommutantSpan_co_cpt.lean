-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_co_cpt
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.co_cpt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:02.74999+00:00
-- url     : https://prove2.me/theorems/b40446f6-904d-408b-8e2d-29702fd01184
-- title:
--   Place Perm Operator Bicommutant Span: co cpt
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the co cpt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L109-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L109-L121

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

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.co_cpt (h : NADual V χ μ) {K : Set V} (hK : IsCompact K) : ∃ L : AddSubgroup V, CO L ∧ K ⊆ L := by sorry
