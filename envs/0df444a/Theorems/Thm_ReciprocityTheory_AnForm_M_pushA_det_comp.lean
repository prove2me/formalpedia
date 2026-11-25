-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_det_comp
-- name    : ReciprocityTheory.AnForm.M.pushA_det_comp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:51:27.050412+00:00
-- url     : https://prove2.me/theorems/cfe68159-653c-4e78-a6ed-db5c6b16e306
-- title:
--   M: push A det comp
-- statement:
--   The M construction uses the push A det comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PushAFinsumInter.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PushAFinsumInter.lean#L52-L56

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

theorem ReciprocityTheory.AnForm.M.pushA_det_comp (f g : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
    LinearMap.det ((f.comp g : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
        LinearMap.det (g : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by sorry
