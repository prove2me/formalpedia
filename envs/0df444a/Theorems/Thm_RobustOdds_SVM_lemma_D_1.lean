-- Prove2me | Theorems.Thm_RobustOdds_SVM_lemma_D_1
-- name    : RobustOdds.SVM.lemma_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:39:10.013366+00:00
-- url     : https://prove2.me/theorems/243399f8-a1cd-48e4-a79d-8c1805b263a8
-- title:
--   Lemma D.1 — equal weak-feature weights
-- statement:
--   Let $p\in[0,1]$ and $\lambda>0$. If $w^*$ globally minimizes the soft-margin SVM objective $J_\lambda$ of (5), then all coefficients of the weak features agree:
--
--   $$w_i^*=w_j^*\qquad(i,j\in\{2,\ldots,d+1\}).$$
--
--   The statement records the symmetry of an optimal SVM solution under exchange of the identically distributed weak coordinates. No unit-norm tuning is needed for this lemma.
-- source:
--   Tsipras et al., Robustness May Be at Odds with Accuracy, arXiv:1805.12152v5, p. 16, Lemma D.1 (proof p. 17)

import Mathlib
import Definitions.Def_RobustOdds_SVM_Setting

namespace RobustOdds.SVM

theorem lemma_D_1 (d : ℕ) (p η : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (lam : ℝ) (hlam : 0 < lam) (w : Fin (d + 1) → ℝ)
    (hmin : ∀ w', svmObj d p η lam w ≤ svmObj d p η lam w') :
    ∀ i j : Fin d, w i.succ = w j.succ := by sorry

end RobustOdds.SVM
