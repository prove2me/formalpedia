-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_symm_hyp_mem
-- name    : ReciprocityTheory.AnForm.M.PLAux.symm_hyp_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:59:36.724553+00:00
-- url     : https://prove2.me/theorems/e678bf93-409e-4fac-a6e9-0ce046a428ed
-- title:
--   PLAux: symm hyp mem
-- statement:
--   The PLAux construction uses the symm hyp mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffHypInclAt.lean#L46-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffHypInclAt.lean#L46-L60

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
variable {A : FinHolAtlas (e + 1) X} {W : Set X} {ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)}
  {i : Fin (e + 1)}

theorem ReciprocityTheory.AnForm.M.PLAux.symm_hyp_mem (hWψ : W ∩ ψ.source = {p ∈ ψ.source | ψ p i = 0}) {z : Fin e → ℂ}
    (hz : hypInclAt i z ∈ ψ.target) :
    ψ.symm (hypInclAt i z) ∈ W ∧ ψ.symm (hypInclAt i z) ∈ ψ.source ∧
      Fin.removeNth i (ψ (ψ.symm (hypInclAt i z))) = z := by sorry
