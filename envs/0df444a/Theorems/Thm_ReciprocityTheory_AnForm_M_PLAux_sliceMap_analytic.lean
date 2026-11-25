-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_sliceMap_analytic
-- name    : ReciprocityTheory.AnForm.M.PLAux.sliceMap_analytic
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:00:50.929731+00:00
-- url     : https://prove2.me/theorems/33cc8e08-318d-4de6-b50e-ac1a106586c6
-- title:
--   PLAux: slice Map analytic
-- statement:
--   The PLAux construction uses the slice Map analytic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffHypInclAt.lean#L73-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffHypInclAt.lean#L73-L96

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffHypInclAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrableOn_image_iff_analytic
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_image_eq_integral_normSq_det_smul
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.PLAux
open MeasureTheory FinHolAtlas Filter Topology
open ReciprocityTheory.AnForm.A (hypInclAt densHypAt jacC maDens_comp integral_image_eq_integral_normSq_det_smul
  integrableOn_image_iff_analytic)
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
variable [T2Space X] [CompactSpace X] {A : FinHolAtlas (e + 1) X} {W : Set X} [CompactSpace W]
  {ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)} {i : Fin (e + 1)}

theorem ReciprocityTheory.AnForm.M.PLAux.sliceMap_analytic (B : FinHolAtlas e W) (hB : HoloMap B A Subtype.val)
    (hψ : IsCompatChart A ψ) (j : Fin B.n) {V : Set X} (hVψ : V ⊆ ψ.source) :
    AnalyticOnNhd ℂ (sliceMap ψ i (B.chart j))
      ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (Subtype.val ⁻¹' V)) := by sorry
