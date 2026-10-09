-- Prove2me | Theorems.Thm_RelSmoothFOM_DOptimal_proposition_2_2
-- name    : RelSmoothFOM.DOptimal.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:31.517768+00:00
-- url     : https://prove2.me/theorems/657d56f3-8fbe-4992-9f86-77ab32609cda
-- title:
--   Proposition 2.2 — one-smoothness relative to the log barrier
-- statement:
--   Let $H\in\mathbb R^{m\times n}$ have rank $m$. For the D-optimal objective $f(x)=-\log\det(H\operatorname{Diag}(x)H^\top)$ and logarithmic barrier $h(x)=-\sum_j\log x_j$, every two positive vectors $x,y$ satisfy
--   $$f(y)\le f(x)+\nabla f(x)\cdot(y-x)+1\cdot D_h(y,x).$$
--   Thus $f$ is relatively smooth with the paper's constant $L=1$ on the positive orthant, which sets the step model in Algorithm 1.
--
--   **Formalization Note** Full row rank is the standing assumption of problem (16). All vector coordinates are positive, so the determinant is positive and no total-logarithm value at zero enters.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 341, Proposition 2.2

import Mathlib
import Definitions.Def_RelSmoothFOM_DOptimal_Setting

namespace RelSmoothFOM.DOptimal

/-- Proposition 2.2: one-smoothness on the positive orthant. -/
theorem proposition_2_2 {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (hH : H.rank = m) :
    ∀ x : Fin n → ℝ, (∀ j, 0 < x j) →
      ∀ y : Fin n → ℝ, (∀ j, 0 < y j) →
        dOptObj H y ≤ dOptObj H x +
          fderiv ℝ (dOptObj H) x (y - x) +
          1 * RelSmoothFOM.PrimalGrad.bregman logBarrier y x := by sorry

end RelSmoothFOM.DOptimal
