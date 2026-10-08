-- Prove2me | Theorems.Thm_SongZipkinFluct_Linear_corollary2
-- name    : SongZipkinFluct.Linear.corollary2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:36:16.920797+00:00
-- url     : https://prove2.me/theorems/42064b44-69db-41bb-80e2-e3a2d127f37f
-- title:
--   Corollary 2 — convergence of finite-stage basestock levels
-- statement:
--   For each world state $i$, the integer sequence of finite-stage smallest minimizers converges to a finite limit $y_\infty^*(i)$. If $y^+_{\min}$ is the smallest myopic basestock level, then for every $n\ge1$,
--
--   $$0\le y^+_{\min}\le y_\infty^*(i)\le y_n^*(i)\le y_1^*(i)=y^+(i).$$
--
--   The limit is an integer because the sequence is bounded and monotone on the integers.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 357, Corollary 2

import Mathlib
import Definitions.Def_SongZipkinFluct_Linear_Dynamics

namespace SongZipkinFluct.Linear

/-- Song and Zipkin (1993), Corollary 2, p. 357. The integer sequence
is indexed by the paper's stage `n≥1`; its convergence is stated via
the zero-based sequence `n ↦ ys (n+1)`. -/
theorem corollary2 {I : Type*} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) (hA : M.Assumption1) :
    ∃ (ys : ℕ → I → ℤ) (yplus yinf : I → ℤ) (ymin : ℤ),
      (∀ i : I, SmallestMinimizer (M.Gplus i) (yplus i)) ∧
      IsLeast (Set.range yplus) ymin ∧
      (∀ n : ℕ, 1 ≤ n → ∀ i : I,
        SmallestMinimizer (M.Glin n i) (ys n i)) ∧
      (∀ i : I, Filter.Tendsto (fun n : ℕ => ys (n + 1) i)
        Filter.atTop (nhds (yinf i))) ∧
      0 ≤ ymin ∧
      ∀ n : ℕ, 1 ≤ n → ∀ i : I,
        ymin ≤ yinf i ∧ yinf i ≤ ys n i ∧
        ys n i ≤ ys 1 i ∧ ys 1 i = yplus i := by sorry

end SongZipkinFluct.Linear
