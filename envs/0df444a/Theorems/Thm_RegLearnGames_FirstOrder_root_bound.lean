-- Prove2me | Theorems.Thm_RegLearnGames_FirstOrder_root_bound
-- name    : RegLearnGames.FirstOrder.root_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:43:54.434983+00:00
-- url     : https://prove2.me/theorems/169f1534-c614-441a-8650-5959b45d934b
-- title:
--   Root bound, supp. p. 10 — the two upper bounds obtained from the quadratic inequality
-- statement:
--   Let $0<\mu<1$ and $a=(1-\mu)/\mu$. If $x\ge0$ satisfies $ax^2+bx+c\le0$, then
--   $$x\le\frac{\mu}{2(1-\mu)}\bigl(-b+\sqrt{b^2-4ac}\bigr)\le\frac{\mu}{1-\mu}\sqrt{b^2-2ac}.$$
--
--   This elementary real inequality is the root estimate used to pass from the quadratic bound to the final average-cost estimate.
--
--   **Formalization Note** The parameter called $c$ in this inequality is named `cq` in Lean so it does not conflict with the game's cost function. Existence of the nonnegative $x$ satisfying the quadratic inequality forces the first discriminant to be nonnegative.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, supp. p. 10 (PDF p. 19), display beginning ‘and solving for x gives’

import Mathlib

namespace RegLearnGames.FirstOrder

/-- The two upper bounds on the nonnegative root in Appendix H. -/
theorem root_bound (mu b cq x : ℝ)
    (hmu₀ : 0 < mu) (hmu₁ : mu < 1) (hx : 0 ≤ x)
    (hquad : (1 - mu) / mu * x ^ 2 + b * x + cq ≤ 0) :
    x ≤ mu / (2 * (1 - mu)) *
        (-b + Real.sqrt (b ^ 2 - 4 * ((1 - mu) / mu) * cq)) ∧
      mu / (2 * (1 - mu)) *
        (-b + Real.sqrt (b ^ 2 - 4 * ((1 - mu) / mu) * cq)) ≤
          mu / (1 - mu) *
            Real.sqrt (b ^ 2 - 2 * ((1 - mu) / mu) * cq) := by sorry

end RegLearnGames.FirstOrder
