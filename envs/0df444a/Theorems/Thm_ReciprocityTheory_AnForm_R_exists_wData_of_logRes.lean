-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_exists_wData_of_logRes
-- name    : ReciprocityTheory.AnForm.R.exists_wData_of_logRes
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:42:53.980908+00:00
-- url     : https://prove2.me/theorems/8e19f570-6eb3-4ec7-93a4-dac9dc049abd
-- title:
--   R: exists w Data of log Res
-- statement:
--   The R construction uses the exists w Data of log Res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WCharts.lean#L99-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WCharts.lean#L99-L199

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsD
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WCharts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.AnForm.R.exists_wData_of_logRes (hQ : FinalTheorems.FinTypeQE)
    {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (hD : IsMultiHomogIdeal D)
    (hrad : P.IsRadical)
    (hsing : ∀ (p : (k : K) → ι k) (y : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval y h = 0) →
      ¬ IsRegularLocalRing (chartLocRing P p y) → ∀ f ∈ D, eval y f = 0)
    (hmin : ∀ q ∈ P.minimalPrimes, IsRelevant q → ¬ D ≤ q)
    (hL : FinalTheorems.LogResStC (projX P hP) (projB P D hP)) :
    Nonempty (WData P D hP) := by sorry
