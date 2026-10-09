-- Prove2me | Theorems.Thm_RobustOdds_SVM_theorem_2_2
-- name    : RobustOdds.SVM.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:39:03.933148+00:00
-- url     : https://prove2.me/theorems/9ec58a4c-386a-44d0-8b89-77fe0e0d581d
-- title:
--   Theorem 2.2 — adversarial training matters
-- statement:
--   For the distribution (3), suppose $d\ge1$, $1/2\le p\le0.975$, and $\eta\ge4/\sqrt d$.
--
--   1. For any $\lambda>0$, if $w^*$ globally minimizes the ordinary soft-margin SVM objective (5) and its squared Euclidean norm is one, the associated linear classifier has standard accuracy strictly above $99\%$ and robust accuracy strictly below $1\%$ at every $\ell_\infty$ radius $\varepsilon\ge2\eta$.
--   2. For any training radius $\varepsilon_{\mathrm{tr}}\ge2\eta$ with $\varepsilon_{\mathrm{tr}}<2p-1$ or $p=1/2$, any $\lambda>0$, and global minimizer $w^*$ of the distributional adversarial objective (2), the associated classifier has standard and robust accuracies exactly $p$ for each evaluation radius $0\le\varepsilon<1$.
--
--   In formulas, the two conclusions are
--
--   $$
--   \Pr_D(f_{w^*}(x)=y)>0.99,\quad \operatorname{RobAcc}_{\varepsilon}(f_{w^*})<0.01;
--   \qquad
--   \Pr_D(f_{w^*}(x)=y)=\operatorname{RobAcc}_{\varepsilon}(f_{w^*})=p
--   $$
--
--   under their respective optimization hypotheses. This is the paper's comparison between standard and adversarial training in one explicit distribution.
--
--   **Formalization Note** $d\ge1$ prevents division by $\sqrt0$. The unit-norm condition is Appendix D's tuning assumption on $\lambda$. The condition "$\varepsilon_{\mathrm{tr}}<2p-1$ or $p=1/2$" is a necessary correction: when $p>1/2$ and $\varepsilon_{\mathrm{tr}}\ge2p-1$ the zero vector is the adversarial minimizer and its constant classifier has accuracy $1/2\ne p$; at $p=1/2$ the same constant classifier has accuracy $1/2=p$, so the printed sentence holds there for every training radius. Evaluation radii are nonnegative so the perturbation ball is nonempty. A score tie is assigned $-1$, irrelevant for the stated nonzero minimizers.
-- source:
--   Tsipras et al., Robustness May Be at Odds with Accuracy, arXiv:1805.12152v5, p. 6, Theorem 2.2; pp. 16–18, App. D

import Mathlib
import Definitions.Def_RobustOdds_SVM_Setting

namespace RobustOdds.SVM

theorem theorem_2_2 (d : ℕ) (hd : 1 ≤ d) (p η : ℝ)
    (hp : 1 / 2 ≤ p) (hp975 : p ≤ 975 / 1000)
    (hη : 4 / Real.sqrt d ≤ η) :
    (∀ lam : ℝ, 0 < lam →
      ∀ w : Fin (d + 1) → ℝ,
        (∀ w', svmObj d p η lam w ≤ svmObj d p η lam w') →
        (∑ i, w i ^ 2) = 1 →
        99 / 100 < RobustOdds.Tradeoff.stdAcc d p η (linClf w) ∧
          ∀ ε : ℝ, 2 * η ≤ ε → RobustOdds.Tradeoff.robustAcc d p η (linClf w) ε < 1 / 100) ∧
    (∀ εtr : ℝ, 2 * η ≤ εtr → (εtr < 2 * p - 1 ∨ p = 1 / 2) →
      ∀ lam : ℝ, 0 < lam →
        ∀ w : Fin (d + 1) → ℝ,
          (∀ w', advObj d p η εtr lam w ≤ advObj d p η εtr lam w') →
          ∀ ε : ℝ, 0 ≤ ε → ε < 1 →
            RobustOdds.Tradeoff.stdAcc d p η (linClf w) = p ∧
              RobustOdds.Tradeoff.robustAcc d p η (linClf w) ε = p) := by sorry

end RobustOdds.SVM
