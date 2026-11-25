-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_exists_local_data_5784ec2a48f6
-- name    : P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_exists_local_data_5784ec2a48f6
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:41:16.954813+00:00
-- url     : https://prove2.me/theorems/4faf2ff1-85c0-5aea-a4be-54e653b60803
-- title:
--   P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral exists local data 5784ec2a48f6: P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral exists local data 5784ec2a48f6
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral exists local data 5784ec2a48f6 construction uses the P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral exists local data 5784ec2a48f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PCoverChartLIntegral.lean#L124-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PCoverChartLIntegral.lean#L124-L140

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsCoverInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PCoverChartLIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm.M MeasureTheory Topology
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.CoverChartLIntegral
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_exists_local_data_5784ec2a48f6 [Nonempty X] {q : X → Fin e → ℂ} {M₀ : Set X} {Δ : Set (Fin e → ℂ)}
    {d : ℕ} (hM : IsOpen M₀) (hΔ : IsClosed Δ) (hmaps : Set.MapsTo q M₀ Δᶜ)
    (hcov : IsCoveringMap hmaps.restrict) (hfib : ∀ z ∉ Δ, (M₀ ∩ q ⁻¹' {z}).encard = d)
    (z : (Δᶜ : Set (Fin e → ℂ))) :
    ∃ U : Set (Fin e → ℂ), IsOpen U ∧ (z : Fin e → ℂ) ∈ U ∧ U ⊆ Δᶜ ∧ ∃ W : Fin d → Set X,
      ∃ s : Fin d → (Fin e → ℂ) → X,
      (∀ i, IsOpen (W i)) ∧ (∀ i, W i ⊆ M₀) ∧ Pairwise (Function.onFun Disjoint W) ∧
      (∀ x ∈ M₀, q x ∈ U → ∃ i, x ∈ W i) ∧ (∀ i, ContinuousOn (s i) U) ∧
      (∀ i, ∀ u ∈ U, s i u ∈ W i ∧ q (s i u) = u) ∧
      (∀ i, ∀ x ∈ W i, q x ∈ U ∧ s i (q x) = x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«CoverChartLIntegral».«exists_local_data» := P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_exists_local_data_5784ec2a48f6
