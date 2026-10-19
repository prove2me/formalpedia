-- Prove2me | Theorems.Thm_UniformPatrol_Star_proposition_2
-- name    : UniformPatrol.Star.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:45.879982+00:00
-- url     : https://prove2.me/theorems/bbebba0d-4e2f-450d-a699-1e8f5665f0a8
-- title:
--   Proposition 2 — odd-duration random walk and game value
-- statement:
--   For odd $m\geq3$, the unique optimal patroller strategy is the zero-holding random walk $(p,s)=(1/n,1)$. Every attacked end and every positive delay is optimal against it. Every saddle point has that same patroller strategy, and the game value is
--
--   $$V=1-\left(\frac{n-1}{n}\right)^{(m-1)/2}.$$
--
--   This case shows why delay two is not uniquely optimal for odd durations.
--
--   **Formalization Note** The exponent is natural-number division, equal to the integer $(m-1)/2$ because $m$ is odd. The mission assumes $n\geq2$.
-- source:
--   Alpern, Chleboun, Katsikas, The Uniformed Patroller Game, arXiv:1908.07366v2, p. 6 (PDF 7), Proposition 2 and eq. (7)

import Mathlib
import Definitions.Def_UniformPatrol_Star_Model

namespace UniformPatrol.Star

/-- Proposition 2: the zero-holding random walk is uniquely optimal at odd durations. -/
theorem proposition_2 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (ho : Odd m) :
    ∃ x : PStrat n, x.p = 1 / (n : ℝ) ∧ x.s = 1 ∧
      (∀ a : AStrat n, IsSaddle n m x a) ∧
      (∀ a : AStrat n,
        Q n m x a = 1 - (((n : ℝ) - 1) / (n : ℝ)) ^ ((m - 1) / 2)) ∧
      (∀ x' : PStrat n, IsOptimalP n m x' →
        x'.p = 1 / (n : ℝ) ∧ x'.s = 1) := by sorry

end UniformPatrol.Star
