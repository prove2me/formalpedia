-- Prove2me | Theorems.Thm_SongZipkinFluct_Linear_theorem2_ab
-- name    : SongZipkinFluct.Linear.theorem2_ab
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:36:44.569875+00:00
-- url     : https://prove2.me/theorems/e0e2b00c-e8ce-4ea7-9418-132584ae58aa
-- title:
--   Theorem 2(a)–(b) — pointwise value limits and minimizers
-- statement:
--   The transformed finite-stage values $W_n$ and auxiliary costs $G_n$ converge pointwise to finite functions $W_\infty$ and $G_\infty$. The first is convex in inventory position and diverges as the position tends upward; the second is convex and diverges at both ends. Consequently $G_\infty(i,\cdot)$ has a finite smallest minimizer $y^*(i)$ in every world state.
--
--   $$W_n(i,x)\to W_\infty(i,x),\qquad G_n(i,y)\to G_\infty(i,y).$$
--
--   These limits are the objects in the infinite-horizon basestock theorem.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 357, Theorem 2, parts (a)–(b)

import Mathlib
import Definitions.Def_SongZipkinFluct_Linear_Dynamics

namespace SongZipkinFluct.Linear

/-- Song and Zipkin (1993), Theorem 2(a)--(b), p. 357. The limits are
the finite pointwise suprema of the nondecreasing sequences from
Theorem 1. The existence of a smallest minimizer is a conclusion. -/
theorem theorem2_ab {I : Type*} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) (hA : M.Assumption1) :
    (∀ i : I, ∀ x : ℤ,
      Filter.Tendsto (fun n : ℕ => M.Wlin n i x) Filter.atTop (nhds (M.Winf i x))) ∧
    (∀ i : I, IntConvex (M.Winf i) ∧
      Filter.Tendsto (M.Winf i) Filter.atTop Filter.atTop) ∧
    (∀ i : I, ∀ y : ℤ,
      Filter.Tendsto (fun n : ℕ => M.Glin (n + 1) i y)
        Filter.atTop (nhds (M.Ginf i y))) ∧
    (∀ i : I, IntConvex (M.Ginf i) ∧ CoerciveInt (M.Ginf i)) ∧
    ∃ ystar : I → ℤ,
      ∀ i : I, SmallestMinimizer (M.Ginf i) (ystar i) := by sorry

end SongZipkinFluct.Linear
