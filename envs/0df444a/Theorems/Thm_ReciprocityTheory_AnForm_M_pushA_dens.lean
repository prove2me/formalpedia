-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_dens
-- name    : ReciprocityTheory.AnForm.M.pushA_dens
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:32:59.16146+00:00
-- url     : https://prove2.me/theorems/748ab8c1-a676-5d5a-b5dc-f0b233f910ef
-- title:
--   M: push A dens
-- statement:
--   The M construction uses the push A dens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PushAFinsumInter.lean#L58-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PushAFinsumInter.lean#L58-L90

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

theorem ReciprocityTheory.AnForm.M.pushA_dens (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    {Q : Set X} {q : X → Fin e → ℂ} (hq : ∀ i, A.HoloOn Q (fun x => q x i))
    (j : Fin A.n) {z : Fin e → ℂ} (hz : z ∈ (A.chart j).target) (hzQ : (A.chart j).symm z ∈ Q)
    (hdet : LinearMap.det (fderiv ℂ (q ∘ (A.chart (chartIdx A ((A.chart j).symm z))).symm)
        (A.chart (chartIdx A ((A.chart j).symm z)) ((A.chart j).symm z)) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) :
    Complex.normSq (LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) z :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) * pushDens A Φ q ((A.chart j).symm z) =
      locDens A Φ j z := by sorry
