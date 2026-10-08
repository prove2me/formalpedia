-- Prove2me | Theorems.Thm_SongZipkinFluct_Linear_corollary1
-- name    : SongZipkinFluct.Linear.corollary1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:31:07.200183+00:00
-- url     : https://prove2.me/theorems/4e51f8f9-f36a-47ed-8f9d-1aaa36c56af3
-- title:
--   Corollary 1 — existence and nonnegativity of myopic levels
-- statement:
--   If $\alpha\bar c\ge p$, each myopic cost $G^+(i,\cdot)$ is nondecreasing, the case denoted $y^+(i)=-\infty$ by the paper. If $\alpha\bar c<p$, every world state has a finite, nonnegative smallest minimizer $y^+(i)$, and its myopic cost is nonnegative everywhere.
--
--   $$y^+(i)\ge0,\qquad G^+(i,y)\ge0\quad(i\in I,\ y\in\mathbb Z).$$
--
--   The latter case is the standing regime for the subsequent linear-cost results.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 356, Corollary 1

import Mathlib
import Definitions.Def_SongZipkinFluct_Linear_Model

namespace SongZipkinFluct.Linear

/-- Song and Zipkin (1993), Corollary 1, p. 356. The paper sets
`y⁺(i)=-∞` when `G⁺(i,·)` is nondecreasing; the first clause states
that monotonicity directly. In the second case a finite smallest
minimizer exists and is nonnegative. -/
theorem corollary1 {I : Type*} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) :
    (M.p ≤ M.α * M.cbar → ∀ i : I, Monotone (M.Gplus i)) ∧
    (M.Assumption1 → ∀ i : I,
      (∃ y : ℤ, SmallestMinimizer (M.Gplus i) y ∧ 0 ≤ y) ∧
      ∀ y : ℤ, 0 ≤ M.Gplus i y) := by sorry

end SongZipkinFluct.Linear
