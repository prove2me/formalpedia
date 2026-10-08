-- Prove2me | Theorems.Thm_PowerTwoChoices_Limit_expected_time_identity
-- name    : PowerTwoChoices.Limit.expected_time_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:21.338989+00:00
-- url     : https://prove2.me/theorems/c7481f4d-cf9b-4e5b-a003-68b658ebad2e
-- title:
--   Proof of Corollary 2, display — $\sum_{i\ge1} i(s_{i-1}^d-s_i^d)=\sum_{i\ge0}s_i^d$
-- statement:
--   Let $d\ge2$ and let $s=(s_0,s_1,\dots)$ be a state of the limiting supermarket system: $s_0=1$, $s_i\ge0$, $s_i$ nonincreasing in $i$. An arriving customer becomes the $i$-th customer in its queue with probability $s_{i-1}^d-s_i^d$. If $s_i\to0$ as $i\to\infty$, then the expected time it spends in the system satisfies
--   $$\sum_{i=1}^\infty i\,(s_{i-1}^d-s_i^d)=\sum_{i=0}^\infty s_i^d ,$$
--   as an identity in $[0,\infty]$.
--
--   This summation by parts turns the expected time into a function of the tails, which is how the convergence of the state to the fixed point becomes convergence of the expected time.
--
--   **Formalization Note.** Both sides are computed in $[0,\infty]$. The hypothesis $s_i\to0$ is implicit in the paper (it holds along every trajectory to which the identity is applied); without it the identity is false.
-- source:
--   Mitzenmacher, The Power of Two Choices in Randomized Load Balancing, IEEE Trans. Parallel Distrib. Syst. 12(10), 2001, p. 1099, proof of Corollary 2, display

import Mathlib
import Definitions.Def_PowerTwoChoices_Limit_SupermarketSystem

open scoped ENNReal
open Filter Topology

namespace PowerTwoChoices.Limit

/-- Proof of Corollary 2, display (Mitzenmacher 2001, p. 1099). For a state `x` whose tails tend
to `0`, the expected time `∑_{i ≥ 1} i (x_{i-1}^d - x_i^d)` equals `∑_{i ≥ 0} x_i^d`
(both sides in `[0, ∞]`). -/
theorem expected_time_identity (d : ℕ) (hd : 2 ≤ d) (x : ℕ → ℝ) (hx : IsState x)
    (hlim : Tendsto x atTop (𝓝 0)) :
    expectedTime d x = ∑' i : ℕ, ENNReal.ofReal (x i ^ d) := by sorry

end PowerTwoChoices.Limit
