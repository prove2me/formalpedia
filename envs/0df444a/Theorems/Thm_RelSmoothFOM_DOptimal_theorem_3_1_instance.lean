-- Prove2me | Theorems.Thm_RelSmoothFOM_DOptimal_theorem_3_1_instance
-- name    : RelSmoothFOM.DOptimal.theorem_3_1_instance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:38:37.131159+00:00
-- url     : https://prove2.me/theorems/747f9b0d-2575-4f3a-96e2-3bde657ed163
-- title:
--   Theorem 3.1 at the positive simplex — the one-over-k estimate
-- statement:
--   Let $H\in\mathbb R^{m\times n}$ have rank $m$ and $n\ge m+1$. Start Algorithm 1 at $x^0=e/n$ on the positive simplex, using the D-optimal objective $f$, log barrier $h$, and $L=1$. For every $k\ge1$ and every positive-simplex comparison point $u$,
--   $$f(x^k)-f(u)\le\frac{D_h(u,x^0)}{k}.$$
--   This is the $\mu=0$ case of the primal gradient bound applied to the comparison point used in Theorem 4.1.
--
--   **Formalization Note** The run takes its argmin over the positive simplex, as the paper's subproblem minimizer has positive coordinates.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), pp. 349–350, application of Theorem 3.1 in proof of Theorem 4.1

import Mathlib
import Definitions.Def_RelSmoothFOM_DOptimal_Setting

namespace RelSmoothFOM.DOptimal

/-- The μ = 0, L = 1 instance of Theorem 3.1 used in Section 4. -/
theorem theorem_3_1_instance {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (hH : H.rank = m) (hmn : m + 1 ≤ n)
    (x : ℕ → Fin n → ℝ) (hx0 : x 0 = fun _ => 1 / (n : ℝ))
    (hrun : RelSmoothFOM.PrimalGrad.IsPrimalGradientRun (posSimplex n) (dOptObj H) logBarrier 1 x) :
    ∀ k : ℕ, 1 ≤ k → ∀ u ∈ posSimplex n,
      dOptObj H (x k) - dOptObj H u ≤
        RelSmoothFOM.PrimalGrad.bregman logBarrier u (x 0) / (k : ℝ) := by sorry

end RelSmoothFOM.DOptimal
