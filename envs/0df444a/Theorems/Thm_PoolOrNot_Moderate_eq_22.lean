-- Prove2me | Theorems.Thm_PoolOrNot_Moderate_eq_22
-- name    : PoolOrNot.Moderate.eq_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:41.982628+00:00
-- url     : https://prove2.me/theorems/b0f5a67a-15a3-4129-8ae5-2d3276d70a7e
-- title:
--   (22), p. 9 — Laplace transform of T_a(i): E[e^{−sT_a(i)}] = ∏_{k<i} (μ+kθ)/(s+μ+kθ)
-- statement:
--   Let $\mu, \theta > 0$ and let $T_a(i)$ be the absorption time of the pure death process with death rate $\mu + \theta(j-1)$ in state $j$, started from $i \ge 1$. For every $s \ge 0$,
--   $$E\bigl[e^{-sT_a(i)}\bigr] = \prod_{k=0}^{i-1} \frac{\mu + k\theta}{s + \mu + k\theta}. \tag{22}$$
--
--   The transform identifies $T_a(i)$, the waiting time of a customer who joins a server with $i$ customers, as a hypoexponential random variable.
--
--   **Formalization Note** The page gives no domain for $s$; the statement uses the Laplace-transform convention $s \ge 0$.
-- source:
--   Cao, He, Huang & Liu, To Pool or Not to Pool: Queueing Design for Large-Scale Service Systems, Operations Research, Articles in Advance (2020), doi:10.1287/opre.2019.1976, p. 9 (PDF 10), (22)

import Mathlib
import Definitions.Def_PoolOrNot_Moderate_Waiting

open MeasureTheory

namespace PoolOrNot.Moderate

/-- **(22)**, p. 9. The Laplace transform of `T_a(i)`:
`E[e^{−s T_a(i)}] = ∏_{k=0}^{i−1} (μ + kθ)/(s + μ + kθ)` for `i ∈ ℕ` (`i ≥ 1`), at `s ≥ 0`. -/
theorem eq_22 (μ θ : ℝ) (hμ : 0 < μ) (hθ : 0 < θ) (i : ℕ) (hi : 1 ≤ i) (s : ℝ) (hs : 0 ≤ s) :
    ∫ x, Real.exp (-s * x) ∂(taLaw μ θ i) =
      ∏ k ∈ Finset.range i, (μ + (k : ℝ) * θ) / (s + μ + (k : ℝ) * θ) := by sorry

end PoolOrNot.Moderate
