-- Prove2me | Theorems.Thm_RobustOdds_SVM_lemma_D_4
-- name    : RobustOdds.SVM.lemma_D_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:41:03.626094+00:00
-- url     : https://prove2.me/theorems/30c49881-1516-40ca-9c94-64262a4ef20a
-- title:
--   Lemma D.4 — robust accuracy at most 1%
-- statement:
--   Assume $d\ge1$, $1/2\le p\le0.975$, $\eta\ge4/\sqrt d$, and $\lambda>0$. Let $w^*$ globally minimize the soft-margin SVM objective (5), with $\sum_i(w_i^*)^2=1$.
--
--   Against all $\ell_\infty$ perturbations of radius $2\eta$, the classifier has robust accuracy
--
--   $$\Pr_D\bigl(\forall\delta,\ \|\delta\|_\infty\le2\eta\Rightarrow f_{w^*}(x+\delta)=y\bigr)\le0.01.$$
--
--   This is the radius and nonstrict inequality in Lemma D.4; Theorem 2.2 states a strict bound for every radius at least $2\eta$.
--
--   **Formalization Note** The robust event uses outer measure because it need not be Borel.
-- source:
--   Tsipras et al., Robustness May Be at Odds with Accuracy, arXiv:1805.12152v5, p. 18, Lemma D.4

import Mathlib
import Definitions.Def_RobustOdds_SVM_Setting

namespace RobustOdds.SVM

theorem lemma_D_4 (d : ℕ) (hd : 1 ≤ d) (p η : ℝ)
    (hp : 1 / 2 ≤ p) (hp975 : p ≤ 975 / 1000) (hη : 4 / Real.sqrt d ≤ η)
    (lam : ℝ) (hlam : 0 < lam) (w : Fin (d + 1) → ℝ)
    (hmin : ∀ w', svmObj d p η lam w ≤ svmObj d p η lam w')
    (hnorm : ∑ i, w i ^ 2 = 1) :
    RobustOdds.Tradeoff.robustAcc d p η (linClf w) (2 * η) ≤ 1 / 100 := by sorry

end RobustOdds.SVM
