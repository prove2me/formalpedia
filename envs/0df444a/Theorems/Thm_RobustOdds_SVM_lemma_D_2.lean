-- Prove2me | Theorems.Thm_RobustOdds_SVM_lemma_D_2
-- name    : RobustOdds.SVM.lemma_D_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:40:00.812241+00:00
-- url     : https://prove2.me/theorems/e7a86e7d-e0ed-43b2-bc13-7fc44e33cbaa
-- title:
--   Lemma D.2 — pooled coefficient at least 1/√2
-- statement:
--   Assume $d\ge1$, $1/2\le p\le0.975$, $\eta\ge4/\sqrt d$, and $\lambda>0$. Let $w^*$ globally minimize the soft-margin SVM objective (5), with $\sum_i(w_i^*)^2=1$.
--
--   The coefficient $v^*$ on $z=d^{-1/2}\sum_{i=2}^{d+1}x_i$ satisfies
--
--   $$v^*=d^{-1/2}\sum_{i=2}^{d+1}w_i^*\ge\frac1{\sqrt2}.$$
--
--   This lower bound quantifies how much weight the standard SVM puts on the weak Gaussian features.
--
--   **Formalization Note** The coefficient is written as the average of the weak weights, so the statement does not presuppose Lemma D.1 as a hypothesis.
-- source:
--   Tsipras et al., Robustness May Be at Odds with Accuracy, arXiv:1805.12152v5, p. 17, Lemma D.2

import Mathlib
import Definitions.Def_RobustOdds_SVM_Setting

namespace RobustOdds.SVM

theorem lemma_D_2 (d : ℕ) (hd : 1 ≤ d) (p η : ℝ)
    (hp : 1 / 2 ≤ p) (hp975 : p ≤ 975 / 1000) (hη : 4 / Real.sqrt d ≤ η)
    (lam : ℝ) (hlam : 0 < lam) (w : Fin (d + 1) → ℝ)
    (hmin : ∀ w', svmObj d p η lam w ≤ svmObj d p η lam w')
    (hnorm : ∑ i, w i ^ 2 = 1) :
    1 / Real.sqrt 2 ≤ (1 / Real.sqrt d) * ∑ i : Fin d, w i.succ := by sorry

end RobustOdds.SVM
