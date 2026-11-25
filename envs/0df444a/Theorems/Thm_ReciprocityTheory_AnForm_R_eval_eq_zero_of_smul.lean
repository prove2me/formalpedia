-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_eval_eq_zero_of_smul
-- name    : ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:07.555326+00:00
-- url     : https://prove2.me/theorems/2d706139-3679-42aa-8a35-455c872cc04f
-- title:
--   R: eval eq zero of smul
-- statement:
--   The R construction uses the eval eq zero of smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/MemConePtsIffChartIdeal.lean#L39-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/MemConePtsIffChartIdeal.lean#L39-L50

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

theorem ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (c : K → ℂ) (y : (Σ k, ι k) → ℂ) (hy : ∀ f ∈ P, eval y f = 0) :
    ∀ f ∈ P, eval (fun q => c q.1 * y q) f = 0 := by sorry
