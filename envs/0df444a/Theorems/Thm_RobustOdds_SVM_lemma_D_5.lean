-- Prove2me | Theorems.Thm_RobustOdds_SVM_lemma_D_5
-- name    : RobustOdds.SVM.lemma_D_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:40:20.790054+00:00
-- url     : https://prove2.me/theorems/6d9b39e0-90a5-4812-8d9c-e30cb8c31700
-- title:
--   Lemma D.5 — adversarial minimizer ignores weak features
-- statement:
--   Assume $0\le p\le1$, $\eta\ge0$, a training radius $\varepsilon_{\mathrm{tr}}\ge2\eta$, and $\lambda>0$. If $w^*$ globally minimizes the distributional adversarial soft-margin objective, then
--
--   $$w_i^*=0\qquad(i=2,\ldots,d+1).$$
--
--   The result says adversarial training removes every Gaussian weak feature from the linear classifier.
--
--   **Formalization Note** The adversarial objective is the per-sample maximum of equation (2). The paper's phrase “for some $i>2$” in the proof is a slip; the lemma itself covers every $i\ge2$.
-- source:
--   Tsipras et al., Robustness May Be at Odds with Accuracy, arXiv:1805.12152v5, p. 18, Lemma D.5

import Mathlib
import Definitions.Def_RobustOdds_SVM_Setting

namespace RobustOdds.SVM

theorem lemma_D_5 (d : ℕ) (p η : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hη0 : 0 ≤ η)
    (εtr : ℝ) (hεtr : 2 * η ≤ εtr)
    (lam : ℝ) (hlam : 0 < lam) (w : Fin (d + 1) → ℝ)
    (hmin : ∀ w', advObj d p η εtr lam w ≤ advObj d p η εtr lam w') :
    ∀ i : Fin d, w i.succ = 0 := by sorry

end RobustOdds.SVM
