-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_sliceMap_injOn
-- name    : ReciprocityTheory.AnForm.M.PLAux.sliceMap_injOn
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:59:58.726888+00:00
-- url     : https://prove2.me/theorems/c796fd0f-ddcc-42b4-8453-92b0106adfea
-- title:
--   PLAux: slice Map inj On
-- statement:
--   The PLAux construction uses the slice Map inj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffHypInclAt.lean#L98-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffHypInclAt.lean#L98-L119

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

theorem ReciprocityTheory.AnForm.M.PLAux.sliceMap_injOn (B : FinHolAtlas e W)
    (hWψ : W ∩ ψ.source = {p ∈ ψ.source | ψ p i = 0}) (j : Fin B.n) {V : Set X}
    (hVψ : V ⊆ ψ.source) :
    Set.InjOn (sliceMap ψ i (B.chart j))
      ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (Subtype.val ⁻¹' V)) := by sorry
