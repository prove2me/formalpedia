-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_integral_chartPartMeasure
-- name    : ReciprocityTheory.AnForm.M.integral_chartPartMeasure
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:40.17903+00:00
-- url     : https://prove2.me/theorems/5f1f2835-7ebc-4c74-a735-1c9614a75852
-- title:
--   M: integral chart Part Measure
-- statement:
--   The M construction uses the integral chart Part Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Measure.lean#L106-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Measure.lean#L106-L136

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

theorem ReciprocityTheory.AnForm.M.integral_chartPartMeasure [CompactSpace X] [T2Space X] [BorelSpace X]
    (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) (g : X → ℝ) (hg : Measurable g)
    (hgi : MIntegrable A Φ g) :
    Integrable g (chartPartMeasure A P Φ s j) ∧
      ∫ x, g x ∂chartPartMeasure A P Φ s j =
        ∫ y in (A.chart j).target, g ((A.chart j).symm y) *
          max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0 := by sorry
