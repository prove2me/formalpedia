-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_isRegularLocalRing_locAt_chart
-- name    : ReciprocityTheory.AnForm.R.isRegularLocalRing_locAt_chart
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:20:42.58562+00:00
-- url     : https://prove2.me/theorems/32d15ff5-1090-48a5-9b4a-60049138c7bb
-- title:
--   R: is Regular Local Ring loc At chart
-- statement:
--   The R construction uses the is Regular Local Ring loc At chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChart.lean#L146-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChart.lean#L146-L238

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial IsLocalRing
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
set_option maxHeartbeats 400000

theorem ReciprocityTheory.AnForm.R.isRegularLocalRing_locAt_chart (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ)
    (hdim : ∀ Q ∈ P.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    {t : ℕ} (G : Fin t → MvPolynomial (Σ k, ι k) ℂ) (hG : ∀ i, ∃ a, IsMultiHomog (G i) a)
    (hspan : Ideal.span (Set.range G) = P)
    (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (hz : ∀ h ∈ chartIdeal P p, eval z h = 0)
    (a : Fin (Fintype.card (Σ k, ι k) - (e + Fintype.card K)) → Fin t)
    (b : Fin (Fintype.card (Σ k, ι k) - (e + Fintype.card K)) → Σ k, ι k)
    (hab : eval z (Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i)))) ≠ 0) :
    IsRegularLocalRing (locAt (chartIdeal P p) z) := by sorry
