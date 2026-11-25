-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_intOn
-- name    : ReciprocityTheory.AnForm.M.pushA_intOn
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:51:43.473243+00:00
-- url     : https://prove2.me/theorems/0144e246-05b1-4ebf-a1ac-db61bb6f60a3
-- title:
--   M: push A int On
-- statement:
--   The M construction uses the push A int On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PushAFinsumInter.lean#L197-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PushAFinsumInter.lean#L197-L217

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
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
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.pushA_intOn [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (P : ChartPartition A)
    (Φ : Fin e → LocPot X) (g : X → ℝ) (hg : MIntegrable A Φ g) (j : Fin A.n) :
    IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
      locDens A Φ j y) (A.chart j).target := by sorry
