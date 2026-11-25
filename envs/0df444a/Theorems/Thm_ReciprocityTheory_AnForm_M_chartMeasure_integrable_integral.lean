-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_chartMeasure_integrable_integral
-- name    : ReciprocityTheory.AnForm.M.chartMeasure_integrable_integral
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:55:32.365957+00:00
-- url     : https://prove2.me/theorems/7585d575-0987-41eb-a0b9-051ea646c449
-- title:
--   M: chart Measure integrable integral
-- statement:
--   The M construction uses the chart Measure integrable integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/MaMeasureB.lean#L111-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/MaMeasureB.lean#L111-L146

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Set Filter Topology
open scoped ContDiff ENNReal NNReal
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [T2Space X]

theorem ReciprocityTheory.AnForm.M.chartMeasure_integrable_integral (A : FinHolAtlas e X) (P : ChartPartition A)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (hPsh : ∀ i, IsPsh A (Φ i))
    (j : Fin A.n) {g : X → ℝ} (hg : Measurable g) (hgi : MIntegrable A Φ g) :
    Integrable g (chartMeasure A P Φ j) ∧
      ∫ x, g x ∂chartMeasure A P Φ j =
        ∫ y in (A.chart j).target, g ((A.chart j).symm y) *
          (P.χ j ((A.chart j).symm y) * locDens A Φ j y) := by sorry
