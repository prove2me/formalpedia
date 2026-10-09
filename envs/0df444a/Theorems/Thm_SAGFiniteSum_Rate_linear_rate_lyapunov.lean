-- Prove2me | Theorems.Thm_SAGFiniteSum_Rate_linear_rate_lyapunov
-- name    : SAGFiniteSum.Rate.linear_rate_lyapunov
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:20:49.527187+00:00
-- url     : https://prove2.me/theorems/405d1886-12e1-4818-9474-e2f0d7994139
-- title:
--   App. B.7, p. 46 — strongly convex case: E(g(xᵏ)) − g(x*) ≤ (1 − δ)ᵏℒ(θ⁰)
-- statement:
--   Assume the standing assumptions of §3 with $n\ge2$, and that $g$ is $\mu$-strongly convex with $\mu>0$. Let $\mathcal L$ be the Lyapunov function with the constants of App. B.5 and $\delta=\min(\frac1{8n},\frac\mu{16L})$. Run SAG with step size $\alpha=\frac1{16L}$ from an arbitrary initial state $\theta^0=(y^0,x^0)$, with indices $i_1,i_2,\dots$ independent and uniform on $\{1,\dots,n\}$. Then for every $k\ge0$,
--   $$
--   \mathbb E\big(g(x^k)\big)-g(x^*)\ \le\ (1-\delta)^k\,\mathcal L(\theta^0).
--   $$
--
--   Combined with the value of $\mathcal L(\theta^0)$ for each initialization, this gives the linear rate of Theorem 1.
--
--   **Formalization Note** The expectation over $k$ i.i.d. uniform indices is `SAGA.Convex.expectIdx n k`, the uniform average over $\{1,\dots,n\}^k$. $\mu>0$ is the page's "strongly-convex case ($\delta>0$)". The initial table is arbitrary.
-- source:
--   Schmidt, Le Roux & Bach, arXiv:1309.2388v2, App. B.7, third display, p. 46

import Mathlib
import Definitions.Def_SAGFiniteSum_Rate_Model
import Definitions.Def_SAGFiniteSum_Rate_Lyapunov

open scoped RealInnerProductSpace

namespace SAGFiniteSum.Rate

/-- B.7, linear rate (arXiv:1309.2388v2, p. 46). With step size `α = 1/(16L)`, `n ≥ 2` and `g`
`μ`-strongly convex with `μ > 0`, SAG from any initial state `θ⁰` satisfies
`E[g(xᵏ)] − g(x*) ≤ (1 − δ)ᵏ ℒ(θ⁰)`, `δ = min(1/(8n), μ/(16L))`, for every `k`. -/
theorem linear_rate_lyapunov {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (hA : SAGAssumptions f f' L xstar) (hn : 2 ≤ n)
    (μ : ℝ) (hμ : 0 < μ)
    (hsc : ConvexOn ℝ Set.univ (fun x => SAGA.Convex.fAvg f x - μ / 2 * ‖x‖ ^ 2))
    (θ0 : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) (k : ℕ) :
    SAGA.Convex.expectIdx n k
        (fun js => SAGA.Convex.fAvg f (sagIter f' (1 / (16 * L)) θ0 js k).2)
        - SAGA.Convex.fAvg f xstar
      ≤ (1 - sagDelta n L μ) ^ k * sagLyap f f' L xstar θ0 := by sorry

end SAGFiniteSum.Rate
