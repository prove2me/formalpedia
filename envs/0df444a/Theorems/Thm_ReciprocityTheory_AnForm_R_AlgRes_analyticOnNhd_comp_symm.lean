-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_AlgRes_analyticOnNhd_comp_symm
-- name    : ReciprocityTheory.AnForm.R.AlgRes.analyticOnNhd_comp_symm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:04:42.850811+00:00
-- url     : https://prove2.me/theorems/17a312bb-6c85-5a7e-ac53-38be4d7880be
-- title:
--   Alg Res: analytic On Nhd comp symm
-- statement:
--   The Alg Res construction uses the analytic On Nhd comp symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AtlasA.lean#L70-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AtlasA.lean#L70-L86

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AtlasA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M Topology Filter
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}

theorem ReciprocityTheory.AnForm.R.AlgRes.analyticOnNhd_comp_symm (R : AlgRes ι P D e)
    {ψ : OpenPartialHomeomorph R.M (Fin e → ℂ)} (hψ : R.GoodChart ψ) {m : ℕ}
    (f : R.M → Fin m → ℂ) (S : Set R.M) (hS : IsOpen S) (j : Fin R.n) (hSj : S ⊆ R.src j)
    (r : Fin m → MvPolynomial (Fin (R.amb j)) ℂ) (hf : ∀ y ∈ S, f y = evalFam r (R.coord j y)) :
    AnalyticOnNhd ℂ (f ∘ ψ.symm) (ψ.target ∩ ψ.symm ⁻¹' S) := by sorry
