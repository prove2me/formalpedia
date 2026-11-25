-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_adjoin_reesChart_eq_top
-- name    : ReciprocityTheory.AnForm.R.adjoin_reesChart_eq_top
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:59:26.718162+00:00
-- url     : https://prove2.me/theorems/01ce4863-0c8e-5ea1-8f40-e285d014faea
-- title:
--   R: adjoin rees Chart eq top
-- statement:
--   The R construction uses the adjoin rees Chart eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsD.lean#L40-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsD.lean#L40-L72

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsD
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

theorem ReciprocityTheory.AnForm.R.adjoin_reesChart_eq_top {R : Type} [CommRing R] (c : ℂ →+* R) {σ : Type} (z : σ → R)
    (hz : ∀ r : R, ∃ f : MvPolynomial σ ℂ, r = eval₂ c z f) {m : ℕ} (g : Fin m → R) (i : Fin m)
    {n : ℕ} (y : Fin n → FinalTheorems.reesChart g i)
    (hyz : ∀ q, ∃ l, y l = algebraMap R _ (z q)) (hyt : ∀ k, ∃ l, y l = fracR g i k) :
    @Algebra.adjoin ℂ (FinalTheorems.reesChart g i) _ _ ((algebraMap R (FinalTheorems.reesChart g i)).comp c).toAlgebra
      (Set.range y) = ⊤ := by sorry
