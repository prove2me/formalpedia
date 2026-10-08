-- Prove2me | Theorems.Thm_SongZipkinFluct_Linear_theorem1_ac
-- name    : SongZipkinFluct.Linear.theorem1_ac
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:36:27.958294+00:00
-- url     : https://prove2.me/theorems/8de4746b-fe5a-41a1-a480-6aa6044c658b
-- title:
--   Theorem 1(a)–(c) — convex finite-stage basestock problems
-- statement:
--   In the zero-fixed-cost model with zero terminal cost, for every $n\ge1$ and every world state $i$, $G_n(i,\cdot)$ is convex and diverges at both ends. It therefore has a finite smallest minimizer $y_n^*(i)$. The finite-stage minimum is attained by ordering up to the greater of the current position and $y_n^*(i)$, and $W_n(i,\cdot)$ is convex.
--
--   $$W_n(i,x)=G_n(i,\max\{x,y_n^*(i)\}).$$
--
--   This is the finite-stage basestock assertion used in the limiting argument.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 357, Theorem 1 (printed "Theorem 4"), parts (a)–(c)

import Mathlib
import Definitions.Def_SongZipkinFluct_Linear_Dynamics

namespace SongZipkinFluct.Linear

/-- Song and Zipkin (1993), Theorem 1(a)--(c), printed "Theorem 4",
p. 357. The finite-horizon problem has `K=0`, `W₀=0` as in §3.1.
Part (b) is the assertion that the minimum in (13) is attained by the
world-dependent basestock decision; `W_n` is the optimal n-stage cost
by the recursion's definition. -/
theorem theorem1_ac {I : Type*} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) (hA : M.Assumption1) :
    ∃ ys : ℕ → I → ℤ,
      (∀ n : ℕ, 1 ≤ n → ∀ i : I,
        IntConvex (M.Glin n i) ∧ CoerciveInt (M.Glin n i) ∧
        SmallestMinimizer (M.Glin n i) (ys n i) ∧
        ∀ x : ℤ, M.Wlin n i x = M.Glin n i (max x (ys n i))) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ i : I, IntConvex (M.Wlin n i) := by sorry

end SongZipkinFluct.Linear
