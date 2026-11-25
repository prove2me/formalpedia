-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_unf
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.unf
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:52:02.117451+00:00
-- url     : https://prove2.me/theorems/fdb15f1b-8891-45de-9fa0-da6af0a90b1e
-- title:
--   Place Perm Operator Bicommutant Span: unf
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the unf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/Nuabs.lean#L8-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/Nuabs.lean#L8-L31

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_Nuabs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix Pointwise
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.unf : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Γ' : Subgroup G) [Countable Γ], Γ' ≤ Γ → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ (Q : Type) (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, γ * (r q)⁻¹ ∈ Γ') → ∃ 𝓕' : Set G, IsFundamentalDomain Γ' 𝓕' μ ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ h in 𝓕, ∑' q, f (r q * h) ∂μ = ∫⁻ h in 𝓕', f h ∂μ := by sorry
