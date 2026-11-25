-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_exists_density
-- name    : ReciprocityTheory.ChartRestriction.DS.HExp.exists_density
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:41.700231+00:00
-- url     : https://prove2.me/theorems/ea310599-79d5-402a-8cad-775318c11f87
-- title:
--   HExp: exists density
-- statement:
--   The HExp construction uses the exists density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/HaarExpA.lean#L133-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/HaarExpA.lean#L133-L224

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HExp
open MeasureTheory Metric Filter Topology Module
open scoped ENNReal NNReal
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (lam nu : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure nu]

theorem ReciprocityTheory.ChartRestriction.DS.HExp.exists_density
    (hq : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ > 0, QInv nu ε δ)
    (hpos : ∀ r > 0, 0 < nu (closedBall (0 : V) r)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      (∀ C : ℝ≥0, c < C → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, nu s ≤ C * lam s) ∧
      (∀ C : ℝ≥0, (C : ℝ≥0∞) < c → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, C * lam s ≤ nu s) := by sorry
