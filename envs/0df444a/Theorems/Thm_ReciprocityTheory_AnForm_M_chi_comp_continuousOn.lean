-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_chi_comp_continuousOn
-- name    : ReciprocityTheory.AnForm.M.chi_comp_continuousOn
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:50:22.053267+00:00
-- url     : https://prove2.me/theorems/a31537da-861a-4797-9cb1-67d7c1b564b2
-- title:
--   M: chi comp continuous On
-- statement:
--   The M construction uses the chi comp continuous On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/MaMeasureB.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/MaMeasureB.lean#L71-L74

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

theorem ReciprocityTheory.AnForm.M.chi_comp_continuousOn {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    (P : ChartPartition A) (j : Fin A.n) :
    ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target := by sorry
