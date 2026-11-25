-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_fou_sb
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.fou_sb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:40:32.953188+00:00
-- url     : https://prove2.me/theorems/9211d051-cb0c-4ae1-8963-2b0249e59319
-- title:
--   Place Perm Operator Bicommutant Span: fou sb
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the fou sb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L255-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L255-L281

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

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.fou_sb {φ : V → ℂ} (hφ : SB φ) : SB (fou χ μ φ) ∧ ∀ x, fou χ μ (fou χ μ φ) x = φ (-x) := by sorry
