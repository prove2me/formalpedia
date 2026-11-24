-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_analyticAt_eval_of_pi
-- name    : ReciprocityTheory.AnForm.R.analyticAt_eval_of_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:18.882675+00:00
-- url     : https://prove2.me/theorems/c7712d47-1569-4cb3-ba05-8a6a22df1a1b
-- title:
--   R: analytic At eval of pi
-- statement:
--   The R construction uses the analytic At eval of pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AtlasA.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AtlasA.lean#L12-L24

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

theorem ReciprocityTheory.AnForm.R.analyticAt_eval_of_pi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {σ : Type*}
    {f : E → σ → ℂ} {z : E} (hf : ∀ l, AnalyticAt ℂ (f · l) z) (p : MvPolynomial σ ℂ) :
    AnalyticAt ℂ (fun x => eval (f x) p) z := by sorry
