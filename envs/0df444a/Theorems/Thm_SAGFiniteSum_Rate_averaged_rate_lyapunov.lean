-- Prove2me | Theorems.Thm_SAGFiniteSum_Rate_averaged_rate_lyapunov
-- name    : SAGFiniteSum.Rate.averaged_rate_lyapunov
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:19:14.035184+00:00
-- url     : https://prove2.me/theorems/fd034c9e-50c4-420c-a03a-ebb8be56486c
-- title:
--   App. B.7, p. 47 — convex case: E[g(x̄ᵏ)] − g(x*) ≤ (32n/k)ℒ(θ⁰), x̄ᵏ = (1/k)Σᵢ₌₀ᵏ⁻¹ xⁱ
-- statement:
--   Assume the standing assumptions of §3 with $n\ge2$ (no strong convexity). Let $\mathcal L$ be the Lyapunov function with the constants of App. B.5. Run SAG with step size $\alpha=\frac1{16L}$ from an arbitrary initial state $\theta^0$, with i.i.d. uniform indices, and let $\bar x^k=\frac1k\sum_{i=0}^{k-1}x^i$. Then for every $k\ge1$,
--   $$
--   \mathbb E\big[g(\bar x^k)\big]-g(x^*)\ \le\ \frac{32n}{k}\,\mathcal L(\theta^0).
--   $$
--
--   Combined with the value of $\mathcal L(\theta^0)$ for each initialization, this gives the $O(n/k)$ rate of Theorem 1.
--
--   **Formalization Note** The expectation is `SAGA.Convex.expectIdx n k`. The average includes $x^0$ and excludes $x^k$, as on the page. The page writes $L(\theta^0)$ for $\mathcal L(\theta^0)$; the Lyapunov function is meant.
-- source:
--   Schmidt, Le Roux & Bach, arXiv:1309.2388v2, App. B.7, last display, p. 47

import Mathlib
import Definitions.Def_SAGFiniteSum_Rate_Model
import Definitions.Def_SAGFiniteSum_Rate_Lyapunov

open scoped RealInnerProductSpace

namespace SAGFiniteSum.Rate

/-- B.7, averaged rate (arXiv:1309.2388v2, p. 47). In the convex case, with step size
`α = 1/(16L)` and `n ≥ 2`, SAG from any initial state `θ⁰` satisfies, for every `k ≥ 1`,
`E[g(x̄ᵏ)] − g(x*) ≤ (32n/k) ℒ(θ⁰)` with `x̄ᵏ = (1/k) ∑_{i=0}^{k-1} xⁱ`. -/
theorem averaged_rate_lyapunov {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (hA : SAGAssumptions f f' L xstar) (hn : 2 ≤ n)
    (θ0 : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) (k : ℕ) (hk : 1 ≤ k) :
    SAGA.Convex.expectIdx n k
        (fun js => SAGA.Convex.fAvg f (avgIter f' (1 / (16 * L)) θ0 js))
        - SAGA.Convex.fAvg f xstar
      ≤ 32 * (n : ℝ) / (k : ℝ) * sagLyap f f' L xstar θ0 := by sorry

end SAGFiniteSum.Rate
