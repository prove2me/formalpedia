-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_orbit_bd
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.orbit_bd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:51:44.639418+00:00
-- url     : https://prove2.me/theorems/2b8fe99f-0e94-542c-8ef3-c7eae9be9648
-- title:
--   Place Perm Operator Bicommutant Span: orbit bd
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the orbit bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/SqPosOfNe.lean#L205-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/SqPosOfNe.lean#L205-L258

import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_SqPosOfNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set Matrix
open scoped ENNReal ComplexConjugate MatrixGroups
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι]
variable [TopologicalSpace R] [MeasurableSpace R] {ψ : AddChar R ℂ} {h : R} {B : Matrix ι ι R} {μ : Measure (ι → R)}
variable (H : NAQuad ψ h B μ)
include H

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.orbit_bd (O : Set R) {L : AddSubgroup (ι → R)} (hL : CO L) (hst : ∀ a ∈ O, ∀ x ∈ L, a • x ∈ L)
    {φ : (ι → R) → ℂ} (hφ : SB φ) (hfix : ∀ x ∈ L, ∀ y ∈ L, Heisenberg₂ ψ h B x y φ = φ) :
    ∃ (L' : AddSubgroup (ι → R)) (s : Finset (ι → R)) (C : ℝ), CO L' ∧ ∀ k : SL(2, R), (∀ i j, k i j ∈ O) →
      ∀ T, Impl ψ h B μ k T → (∀ u, ‖T φ u‖ ≤ C) ∧ ∃ c : (ι → R) → ℂ, (∀ a, ‖c a‖ ≤ C) ∧ T φ = ∑ a ∈ s, c a • ind a L' := by sorry
