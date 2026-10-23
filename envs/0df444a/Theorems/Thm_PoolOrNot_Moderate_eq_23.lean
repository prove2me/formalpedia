-- Prove2me | Theorems.Thm_PoolOrNot_Moderate_eq_23
-- name    : PoolOrNot.Moderate.eq_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:40.942998+00:00
-- url     : https://prove2.me/theorems/996ef949-cf74-44fe-9361-f33679efc29f
-- title:
--   (23), p. 9 — the complementary distribution function of T_a(i)
-- statement:
--   Let $\mu, \theta > 0$ and $i \ge 1$. For every $x \ge 0$,
--   $$P\bigl(T_a(i) > x\bigr) = \sum_{j=1}^{i} e^{-(\mu + (j-1)\theta)x} \prod_{\substack{k=1\\ k \ne j}}^{i} \frac{\mu + (k-1)\theta}{(k-j)\theta}. \tag{23}$$
--
--   With (22) this gives the explicit distribution of the waiting time of a customer who joins a server with $i$ customers, from which service levels $P(W \le x)$ are computed.
--
--   **Formalization Note** $k - j$ is a real difference (negative for $k < j$). The rates $\mu + (k-1)\theta$ are distinct because $\theta > 0$.
-- source:
--   Cao, He, Huang & Liu, To Pool or Not to Pool: Queueing Design for Large-Scale Service Systems, Operations Research, Articles in Advance (2020), doi:10.1287/opre.2019.1976, p. 9 (PDF 10), (23)

import Mathlib
import Definitions.Def_PoolOrNot_Moderate_Waiting

open MeasureTheory

namespace PoolOrNot.Moderate

/-- **(23)**, p. 9. The complementary distribution function of `T_a(i)`, `i ≥ 1`, `x ≥ 0`:
`P(T_a(i) > x) = Σ_{j=1}^{i} e^{−(μ+(j−1)θ)x} ∏_{k=1, k≠j}^{i} (μ + (k−1)θ)/((k − j)θ)`. -/
theorem eq_23 (μ θ : ℝ) (hμ : 0 < μ) (hθ : 0 < θ) (i : ℕ) (hi : 1 ≤ i) (x : ℝ) (hx : 0 ≤ x) :
    (taLaw μ θ i (Set.Ioi x)).toReal =
      ∑ j ∈ Finset.Icc 1 i, Real.exp (-(μ + ((j : ℝ) - 1) * θ) * x) *
        ∏ k ∈ (Finset.Icc 1 i).erase j, (μ + ((k : ℝ) - 1) * θ) / (((k : ℝ) - (j : ℝ)) * θ) := by sorry

end PoolOrNot.Moderate
