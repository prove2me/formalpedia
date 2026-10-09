-- Prove2me | Theorems.Thm_SAGFiniteSum_Rate_summed_suboptimality
-- name    : SAGFiniteSum.Rate.summed_suboptimality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:33.683531+00:00
-- url     : https://prove2.me/theorems/6fde01da-1b33-4fb0-b208-126ffea150ef
-- title:
--   App. B.7, pp. 46–47 — convex case: (1/32n) Σᵢ₌₁ᵏ [E(g(xⁱ⁻¹)) − g(x*)] ≤ ℒ(θ⁰)
-- statement:
--   Assume the standing assumptions of §3 with $n\ge2$ (no strong convexity). Let $\mathcal L$ be the Lyapunov function with the constants of App. B.5. Run SAG with step size $\alpha=\frac1{16L}$ from an arbitrary initial state $\theta^0$, with i.i.d. uniform indices. Then for every $k\ge0$,
--   $$
--   \frac1{32n}\sum_{i=1}^k\Big[\mathbb E\big(g(x^{i-1})\big)-g(x^*)\Big]\ \le\ \mathcal L(\theta^0).
--   $$
--
--   This is the telescoped form of the one-step decrease with $\delta=0$; with Jensen's inequality it gives the $O(n/k)$ rate for the averaged iterate.
--
--   **Formalization Note** The sum over $i=1,\dots,k$ of $g(x^{i-1})$ is written as the sum over $i=0,\dots,k-1$ of $g(x^i)$. Each $\mathbb E\,g(x^i)$ is taken over $k$ i.i.d. uniform indices (`expectIdx n k`), of which $x^i$ uses the first $i$; this is the same number as the expectation over $i$ indices. The page writes $L(\theta)$ for $\mathcal L(\theta)$ in the last display; the Lyapunov function is meant, not the constant $L$. The intermediate terms of the display (telescoping, $\mathbb E\,\mathcal L(\theta^k)\ge0$) are proof steps.
-- source:
--   Schmidt, Le Roux & Bach, arXiv:1309.2388v2, App. B.7, pp. 46–47 (summed display, p. 47)

import Mathlib
import Definitions.Def_SAGFiniteSum_Rate_Model
import Definitions.Def_SAGFiniteSum_Rate_Lyapunov

open scoped RealInnerProductSpace

namespace SAGFiniteSum.Rate

/-- B.7, summed bound (arXiv:1309.2388v2, pp. 46–47). In the convex case, with step size
`α = 1/(16L)` and `n ≥ 2`, SAG from any initial state `θ⁰` satisfies, for every `k`,
`(1/(32n)) ∑_{i=0}^{k-1} [E g(xⁱ) − g(x*)] ≤ ℒ(θ⁰)`. -/
theorem summed_suboptimality {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (hA : SAGAssumptions f f' L xstar) (hn : 2 ≤ n)
    (θ0 : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) (k : ℕ) :
    1 / (32 * (n : ℝ)) * ∑ i ∈ Finset.range k,
        (SAGA.Convex.expectIdx n k
          (fun js => SAGA.Convex.fAvg f (sagIter f' (1 / (16 * L)) θ0 js i).2)
          - SAGA.Convex.fAvg f xstar)
      ≤ sagLyap f f' L xstar θ0 := by sorry

end SAGFiniteSum.Rate
