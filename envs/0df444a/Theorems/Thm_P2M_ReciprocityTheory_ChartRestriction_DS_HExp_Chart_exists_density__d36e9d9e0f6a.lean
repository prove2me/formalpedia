-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_exists_density__d36e9d9e0f6a
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_exists_density__d36e9d9e0f6a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:43:04.80638+00:00
-- url     : https://prove2.me/theorems/4ecff977-6197-5441-bad6-71e4c1182c8a
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HExp Chart exists density  d36e9d9e0f6a: P2 M Reciprocity Theory Chart Restriction DS HExp Chart exists density  d36e9d9e0f6a
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HExp Chart exists density  d36e9d9e0f6a construction uses the P2 M Reciprocity Theory Chart Restriction DS HExp Chart exists density  d36e9d9e0f6a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/HaarExpB.lean#L362-L374
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/HaarExpB.lean#L362-L374

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HExp
open MeasureTheory Filter Topology Metric NormedSpace Set
open scoped ENNReal NNReal
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_exists_density__d36e9d9e0f6a {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G]
    (C : Chart V G) (_hfd : FiniteDimensional ℝ V) (mV : MeasurableSpace V) (_hbV : BorelSpace V)
    (mG : MeasurableSpace G) (_hbG : BorelSpace G) (_hG : IsTopologicalGroup G)
    (μ : Measure G) (_hμ : μ.IsHaarMeasure) (lam : Measure V) (_hlam : lam.IsAddHaarMeasure) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ S : ℝ → Set V, (∀ r, MeasurableSet (S r)) →
      (∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ X ∈ S r, ‖(X : 𝔸)‖ < δ) →
      (∀ᶠ r in 𝓝[>] (0 : ℝ), lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤) →
      Tendsto (fun r => μ {g | ∃ X ∈ S r, C.mat g = exp ((X : V) : 𝔸)} / lam (S r)) (𝓝[>] 0) (𝓝 c) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HExp».«Chart».«exists_density'» := P2M_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_exists_density__d36e9d9e0f6a
