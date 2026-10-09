-- Prove2me | Theorems.Thm_RelSmoothFOM_DOptimal_theorem_4_1
-- name    : RelSmoothFOM.DOptimal.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:44.837148+00:00
-- url     : https://prove2.me/theorems/55efe377-dd41-478b-9f01-ce37516d2d35
-- title:
--   Theorem 4.1 — ε-accuracy for D-optimal design
-- statement:
--   Let $H\in\mathbb R^{m\times n}$ have rank $m$, with $n\ge m+1$. Run the primal gradient scheme on the positive simplex for $f(x)=-\log\det(H\operatorname{Diag}(x)H^\top)$, using the log barrier, relative-smoothness constant $1$, and $x^0=e/n$. Let $x^*$ attain the minimum among feasible simplex points where the information matrix is positive definite, and write $f^*=f(x^*)$. If $0<\varepsilon\le f(x^0)-f^*$ and
--   $$k\ge\frac{2n\log\!\left(2(f(x^0)-f^*)/\varepsilon\right)}{\varepsilon},$$
--   then $f(x^k)-f^*\le\varepsilon$.
--
--   This gives the paper's explicit iteration count for reaching a prescribed optimality gap in D-optimal design.
--
--   **Formalization Note** Positive $\varepsilon$ makes the division and logarithm meaningful. The optimum is represented by an attained $x^*$ on the positive-definiteness domain; the run is over the positive simplex because the log barrier is infinite at the boundary in the paper. Iterates start at index zero.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 349, Theorem 4.1

import Mathlib
import Definitions.Def_RelSmoothFOM_DOptimal_Setting

namespace RelSmoothFOM.DOptimal

/-- Theorem 4.1: iteration complexity for D-optimal design. -/
theorem theorem_4_1 {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (hH : H.rank = m) (hmn : m + 1 ≤ n)
    (x : ℕ → Fin n → ℝ) (hx0 : x 0 = fun _ => 1 / (n : ℝ))
    (hrun : RelSmoothFOM.PrimalGrad.IsPrimalGradientRun (posSimplex n) (dOptObj H) logBarrier 1 x)
    (xstar : Fin n → ℝ) (hxs : xstar ∈ stdSimplex ℝ (Fin n))
    (hxspd : (H * Matrix.diagonal xstar * H.transpose).PosDef)
    (hopt : ∀ y ∈ stdSimplex ℝ (Fin n),
      (H * Matrix.diagonal y * H.transpose).PosDef →
        dOptObj H xstar ≤ dOptObj H y)
    (ε : ℝ) (hε : 0 < ε)
    (hεle : ε ≤ dOptObj H (x 0) - dOptObj H xstar)
    (k : ℕ)
    (hk : 2 * (n : ℝ) *
      Real.log (2 * (dOptObj H (x 0) - dOptObj H xstar) / ε) / ε ≤ (k : ℝ)) :
    dOptObj H (x k) - dOptObj H xstar ≤ ε := by sorry

end RelSmoothFOM.DOptimal
