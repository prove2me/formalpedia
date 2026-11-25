-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_eval_smul_of_isMultiHomog
-- name    : ReciprocityTheory.AnForm.R.eval_smul_of_isMultiHomog
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:37:14.874825+00:00
-- url     : https://prove2.me/theorems/8d24289b-023b-4acc-9892-7ebce4386422
-- title:
--   R: eval smul of is Multi Homog
-- statement:
--   The R construction uses the eval smul of is Multi Homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/MemConePtsIffChartIdeal.lean#L24-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/MemConePtsIffChartIdeal.lean#L24-L37

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.AnForm.R.eval_smul_of_isMultiHomog {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) (c : K → ℂ) (y : (Σ k, ι k) → ℂ) :
    eval (fun q => c q.1 * y q) f = (∏ k, c k ^ a k) * eval y f := by sorry
