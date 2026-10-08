-- Prove2me | Theorems.Thm_TalagrandConc_TSP_sparse_squares
-- name    : TalagrandConc.TSP.sparse_squares
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:21.174567+00:00
-- url     : https://prove2.me/theorems/b3a63a2f-23a5-47a5-be21-4205ab9323c9
-- title:
--   Proposition 11.1.4 — simultaneous bounds on sparse dyadic squares
-- statement:
--   There is a universal constant $K>0$ such that the following holds for $N\ge1$ independent uniform points in $[0,1]^2$ and $1\le t\le\sqrt N/K$. Let $k_0$ be the largest integer satisfying $2^{2k_0}\le N$, and let $k_1$ be the level selected by criterion (11.1.9) with auxiliary Poisson intensity $N/8$. Then $1\le k_1\le k_0$ and
--   $$\frac1K\log\frac N{t^2}\le 2^{2(k_0-k_1)}\le K\log\frac N{t^2}.$$
--
--   Let $m_k$ count level-$k$ squares containing at most $N2^{-2k-6}$ distinct sample locations. With probability at least $1-Ke^{-t^2}$, simultaneously for every $k_1\le k\le k_0$,
--   $$m_k\le K2^{2k}\exp(-N2^{-2k-6}),\qquad m_{k_1-1}\le K\frac{2^{2k_1}t^2}{N}.$$
--
--   This result controls the number of low-occupancy squares over all relevant spatial scales.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), pp. 172–173, Proposition 11.1.4, Eqs. (11.1.12)–(11.1.15)

import Mathlib
import Definitions.Def_TalagrandConc_TSP_Basic

namespace TalagrandConc.TSP

open MeasureTheory

/-- Talagrand (1995), Proposition 11.1.4, pp. 172–173. The integer `k1`
is the choice made in the paper's proof via (11.1.9), with `μ=N/8`. -/
theorem sparse_squares :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (t : ℝ), 0 < N → 1 ≤ t →
      t ≤ Real.sqrt N / K →
      1 ≤ k1 N t ∧ k1 N t ≤ k0 N ∧ k1Criterion N t (k1 N t) ∧
      (1 / K) * Real.log ((N : ℝ) / t ^ 2) ≤
        (2 : ℝ) ^ (2 * (k0 N - k1 N t)) ∧
      (2 : ℝ) ^ (2 * (k0 N - k1 N t)) ≤
        K * Real.log ((N : ℝ) / t ^ 2) ∧
      ENNReal.ofReal (1 - K * Real.exp (-t ^ 2)) ≤
        sampleLaw N {x | (∀ k : ℕ, k1 N t ≤ k → k ≤ k0 N →
          (holeCount N (sampleSet x) k : ℝ) ≤
            K * (2 : ℝ) ^ (2 * k) *
              Real.exp (-(N : ℝ) * (2 : ℝ) ^ (-(2 * k + 6 : ℕ) : ℤ))) ∧
          (holeCount N (sampleSet x) (k1 N t - 1) : ℝ) ≤
            K * (2 : ℝ) ^ (2 * k1 N t) * t ^ 2 / N} := by sorry

end TalagrandConc.TSP
