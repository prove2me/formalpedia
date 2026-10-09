-- Prove2me | Theorems.Thm_RobustOdds_SVM_lemma_D_3
-- name    : RobustOdds.SVM.lemma_D_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:40:42.817815+00:00
-- url     : https://prove2.me/theorems/06cde728-c037-4f9e-9f58-61d12d6e6ce5
-- title:
--   Lemma D.3 — standard accuracy at least 99%
-- statement:
--   Assume $d\ge1$, $1/2\le p\le0.975$, $\eta\ge4/\sqrt d$, and $\lambda>0$. Let $w^*$ globally minimize the soft-margin SVM objective (5), with $\sum_i(w_i^*)^2=1$.
--
--   The linear classifier with weights $w^*$ has standard accuracy
--
--   $$\Pr_D(f_{w^*}(x)=y)\ge0.99.$$
--
--   This is the nonstrict accuracy claim stated in Lemma D.3; the main theorem states a strict bound.
-- source:
--   Tsipras et al., Robustness May Be at Odds with Accuracy, arXiv:1805.12152v5, p. 18, Lemma D.3

import Mathlib
import Definitions.Def_RobustOdds_SVM_Setting

namespace RobustOdds.SVM

theorem lemma_D_3 (d : ℕ) (hd : 1 ≤ d) (p η : ℝ)
    (hp : 1 / 2 ≤ p) (hp975 : p ≤ 975 / 1000) (hη : 4 / Real.sqrt d ≤ η)
    (lam : ℝ) (hlam : 0 < lam) (w : Fin (d + 1) → ℝ)
    (hmin : ∀ w', svmObj d p η lam w ≤ svmObj d p η lam w')
    (hnorm : ∑ i, w i ^ 2 = 1) :
    99 / 100 ≤ RobustOdds.Tradeoff.stdAcc d p η (linClf w) := by sorry

end RobustOdds.SVM
