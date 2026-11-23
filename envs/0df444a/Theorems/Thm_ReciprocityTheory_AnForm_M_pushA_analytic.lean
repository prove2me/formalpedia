-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_analytic
-- name    : ReciprocityTheory.AnForm.M.pushA_analytic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:38:41.698907+00:00
-- url     : https://prove2.me/theorems/687c14c8-8a7c-482c-ba97-8bf444456200
-- title:
--   M: push A analytic
-- statement:
--   The M construction uses the push A analytic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PushAFinsumInter.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PushAFinsumInter.lean#L44-L50

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

theorem ReciprocityTheory.AnForm.M.pushA_analytic (A : FinHolAtlas e X) {Q : Set X} {q : X → Fin e → ℂ}
    (hq : ∀ i, A.HoloOn Q (fun x => q x i)) (j : Fin A.n) {z : Fin e → ℂ}
    (hz : z ∈ (A.chart j).target) (hzQ : (A.chart j).symm z ∈ Q) :
    AnalyticAt ℂ (q ∘ (A.chart j).symm) z := by sorry
