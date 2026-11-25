-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_exists_relevant_minimalPrime_of_chart
-- name    : ReciprocityTheory.AnForm.R.exists_relevant_minimalPrime_of_chart
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:29:05.302946+00:00
-- url     : https://prove2.me/theorems/1b3e630b-33ea-47c6-a6c6-617f1d960805
-- title:
--   R: exists relevant minimal Prime of chart
-- statement:
--   The R construction uses the exists relevant minimal Prime of chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypB.lean#L11-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypB.lean#L11-L120

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypB
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
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.AnForm.R.exists_relevant_minimalPrime_of_chart {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hP : IsMultiHomogIdeal P) (hD : IsMultiHomogIdeal D) (p : (k : K) → ι k)
    (M : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hM : M ∈ (chartIdeal P p).minimalPrimes)
    (hDM : D ≤ M) :
    ∃ q ∈ P.minimalPrimes, IsRelevant q ∧ D ≤ q := by sorry
