-- Prove2me | Theorems.Thm_SAGFiniteSum_Rate_lyapunov_init_zero
-- name    : SAGFiniteSum.Rate.lyapunov_init_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:19:27.743582+00:00
-- url     : https://prove2.me/theorems/ce083693-be50-4174-9263-2e88c6962dd1
-- title:
--   App. B.8.1, p. 47 — with y⁰ = 0: ℒ(θ⁰) ≤ g(x⁰) − g(x*) + σ²/(16L) + (4L/n)‖x⁰ − x*‖²
-- statement:
--   Assume the standing assumptions of §3 with $n\ge2$, and let $\mathcal L$ be the Lyapunov function with the constants of App. B.5. For the initial state $\theta^0=(0,x^0)$ (zero table),
--   $$
--   \mathcal L(\theta^0)\ \le\ g(x^0)-g(x^*)+\frac{\sigma^2}{16L}+\frac{4L}{n}\|x^0-x^*\|^2,
--   \qquad \sigma^2=\frac1n\sum_{i=1}^n\|f'_i(x^*)\|^2 .
--   $$
--
--   This is Theorem 1's constant $C_0$ for the zero initialization.
--
--   **Formalization Note** Only the final inequality of B.8.1 is stated; the two expansions of $\mathcal L(\theta^0)$ that precede it are proof steps. The page notes $e^\top f'(x^*)=0$, which follows from the standing assumptions ($x^*$ minimizes the differentiable $g$).
-- source:
--   Schmidt, Le Roux & Bach, arXiv:1309.2388v2, App. B.8.1, p. 47

import Mathlib
import Definitions.Def_SAGFiniteSum_Rate_Model
import Definitions.Def_SAGFiniteSum_Rate_Lyapunov

open scoped RealInnerProductSpace

namespace SAGFiniteSum.Rate

/-- B.8.1 (arXiv:1309.2388v2, p. 47). With the B.5 constants and `n ≥ 2`, the initial value of
the Lyapunov function at `θ⁰ = (0, x⁰)` satisfies
`ℒ(θ⁰) ≤ g(x⁰) − g(x*) + σ²/(16L) + (4L/n)‖x⁰ − x*‖²`. -/
theorem lyapunov_init_zero {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (hA : SAGAssumptions f f' L xstar) (hn : 2 ≤ n)
    (x0 : EuclideanSpace ℝ (Fin p)) :
    sagLyap f f' L xstar (zeroTable, x0)
      ≤ SAGA.Convex.fAvg f x0 - SAGA.Convex.fAvg f xstar + sigmaSq f' xstar / (16 * L)
        + 4 * L / (n : ℝ) * ‖x0 - xstar‖ ^ 2 := by sorry

end SAGFiniteSum.Rate
