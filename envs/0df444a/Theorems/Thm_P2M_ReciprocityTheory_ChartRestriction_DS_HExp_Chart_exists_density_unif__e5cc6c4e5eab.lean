-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_exists_density_unif__e5cc6c4e5eab
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_exists_density_unif__e5cc6c4e5eab
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:11:52.398687+00:00
-- url     : https://prove2.me/theorems/d387992f-b478-4a3b-8edf-141717b23421
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HExp Chart exists density unif  e5cc6c4e5eab: P2 M Reciprocity Theory Chart Restriction DS HExp Chart exists density unif  e5cc6c4e5eab
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HExp Chart exists density unif  e5cc6c4e5eab construction uses the P2 M Reciprocity Theory Chart Restriction DS HExp Chart exists density unif  e5cc6c4e5eab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/HaarExpB.lean#L376-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/HaarExpB.lean#L376-L385

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_exists_density_unif__e5cc6c4e5eab {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G]
    (C : Chart V G) (_hfd : FiniteDimensional ℝ V) (mV : MeasurableSpace V) (_hbV : BorelSpace V)
    (mG : MeasurableSpace G) (_hbG : BorelSpace G) (_hG : IsTopologicalGroup G)
    (μ : Measure G) (_hμ : μ.IsHaarMeasure) (lam : Measure V) (_hlam : lam.IsAddHaarMeasure) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      (∀ D : ℝ≥0, c < D → ∃ δ > 0, ∀ s : Set V, MeasurableSet s → s ⊆ ball (0 : V) δ →
        μ (C.img s) ≤ D * lam s) ∧
      (∀ D : ℝ≥0, (D : ℝ≥0∞) < c → ∃ δ > 0, ∀ s : Set V, MeasurableSet s → s ⊆ ball (0 : V) δ →
        D * lam s ≤ μ (C.img s)) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HExp».«Chart».«exists_density_unif'» := P2M_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_exists_density_unif__e5cc6c4e5eab
