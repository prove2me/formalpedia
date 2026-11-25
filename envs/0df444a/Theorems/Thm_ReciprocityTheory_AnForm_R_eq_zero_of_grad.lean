-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_eq_zero_of_grad
-- name    : ReciprocityTheory.AnForm.R.eq_zero_of_grad
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:37:34.381901+00:00
-- url     : https://prove2.me/theorems/72cc636d-d88f-58bf-8cf2-f2e7d8030bfd
-- title:
--   R: eq zero of grad
-- statement:
--   The R construction uses the eq zero of grad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AnChartA.lean#L110-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AnChartA.lean#L110-L164

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChartA
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
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.R.eq_zero_of_grad (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) {e : ℕ}
    [IsLocalRing (locRing K p)] (r : Fin e → MvPolynomial (Fin n) ℂ)
    (hr : Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) =
      Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p)) (ptIdeal p))
    {c : ℕ} (F : Fin c → MvPolynomial (Fin n) ℂ) (hFK : ∀ i, F i ∈ K)
    (hh : MvPolynomial (Fin n) ℂ) (hhp : eval p hh ≠ 0)
    (hcut : ∀ g ∈ K, hh * g ∈ Ideal.span (Set.range F)) (v : Fin n → ℂ)
    (hvr : ∀ i, ∑ j, eval p (pderiv j (r i)) * v j = 0)
    (hvF : ∀ k, ∑ j, eval p (pderiv j (F k)) * v j = 0) : v = 0 := by sorry
