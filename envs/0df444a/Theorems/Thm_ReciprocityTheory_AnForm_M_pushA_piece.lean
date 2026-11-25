-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_piece
-- name    : ReciprocityTheory.AnForm.M.pushA_piece
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:51:37.756073+00:00
-- url     : https://prove2.me/theorems/7d629260-abdf-4ea9-90eb-227d04638b98
-- title:
--   M: push A piece
-- statement:
--   The M construction uses the push A piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PushAFinsumInter.lean#L115-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PushAFinsumInter.lean#L115-L147

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

theorem ReciprocityTheory.AnForm.M.pushA_piece (q : X → Fin e → ℂ) (s : (Fin e → ℂ) → X) {D : Set (Fin e → ℂ)}
    (hD : MeasurableSet D) (hdiff : ∀ z ∈ D, DifferentiableAt ℂ (q ∘ s) z)
    (hinj : Set.InjOn (q ∘ s) D) (k : X → ℝ) :
    (Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} ∩ s '' D, k x) ↔
      IntegrableOn (fun z => Complex.normSq (LinearMap.det (fderiv ℂ (q ∘ s) z :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) * k (s z)) D) ∧
    ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} ∩ s '' D, k x =
      ∫ z in D, Complex.normSq (LinearMap.det (fderiv ℂ (q ∘ s) z :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) * k (s z) := by sorry
