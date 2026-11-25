-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_hasSum_ind
-- name    : ReciprocityTheory.AnForm.M.pushA_hasSum_ind
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:51:53.980801+00:00
-- url     : https://prove2.me/theorems/c2fcc972-1501-4c54-a4f3-2a23aecf9313
-- title:
--   M: push A has Sum ind
-- statement:
--   The M construction uses the push A has Sum ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PushAFinsumInter.lean#L235-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PushAFinsumInter.lean#L235-L249

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

theorem ReciprocityTheory.AnForm.M.pushA_hasSum_ind (E : ℕ → Set X) (hE : Pairwise (Function.onFun Disjoint E)) (f : X → ℝ)
    (x : X) : HasSum (fun m => (E m).indicator f x) ((⋃ m, E m).indicator f x) := by sorry
