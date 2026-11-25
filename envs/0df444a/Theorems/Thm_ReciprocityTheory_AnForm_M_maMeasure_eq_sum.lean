-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_maMeasure_eq_sum
-- name    : ReciprocityTheory.AnForm.M.maMeasure_eq_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:50:31.093155+00:00
-- url     : https://prove2.me/theorems/21251a89-a455-43ed-b73a-7f0cb1b81147
-- title:
--   M: ma Measure eq sum
-- statement:
--   The M construction uses the ma Measure eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/MaMeasureB.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/MaMeasureB.lean#L19-L24

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

theorem ReciprocityTheory.AnForm.M.maMeasure_eq_sum {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (hne : Nonempty (ChartPartition A)) :
    maMeasure A Φ = ∑ j, chartMeasure A hne.some Φ j := by sorry
