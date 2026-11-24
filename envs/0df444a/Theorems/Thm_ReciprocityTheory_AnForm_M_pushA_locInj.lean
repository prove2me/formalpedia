-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_locInj
-- name    : ReciprocityTheory.AnForm.M.pushA_locInj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:41.731793+00:00
-- url     : https://prove2.me/theorems/6fea83ef-db79-4f9b-8083-5c7540d28e28
-- title:
--   M: push A loc Inj
-- statement:
--   The M construction uses the push A loc Inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PushAFinsumInter.lean#L158-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PushAFinsumInter.lean#L158-L170

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

theorem ReciprocityTheory.AnForm.M.pushA_locInj {τ : (Fin e → ℂ) → (Fin e → ℂ)} {z : Fin e → ℂ} (hτ : AnalyticAt ℂ τ z)
    (hd : LinearMap.det (fderiv ℂ τ z : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) :
    ∃ W : Set (Fin e → ℂ), IsOpen W ∧ z ∈ W ∧ Set.InjOn τ W := by sorry
