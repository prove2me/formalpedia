-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_chart_weight_compact
-- name    : ReciprocityTheory.AnForm.M.chart_weight_compact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:43.570999+00:00
-- url     : https://prove2.me/theorems/ee7a0659-cddd-4a33-8f5b-93ae2cf74dc9
-- title:
--   M: chart weight compact
-- statement:
--   The M construction uses the chart weight compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Measure.lean#L18-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Measure.lean#L18-L32

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Measure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]

theorem ReciprocityTheory.AnForm.M.chart_weight_compact [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X) (j : Fin A.n) :
    IsCompact ((A.chart j) '' tsupport (P.χ j)) ∧
      (A.chart j) '' tsupport (P.χ j) ⊆ (A.chart j).target ∧
      ∀ y ∈ (A.chart j).target, y ∉ (A.chart j) '' tsupport (P.χ j) →
        P.χ j ((A.chart j).symm y) = 0 := by sorry
