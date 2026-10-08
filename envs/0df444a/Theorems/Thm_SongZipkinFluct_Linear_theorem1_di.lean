-- Prove2me | Theorems.Thm_SongZipkinFluct_Linear_theorem1_di
-- name    : SongZipkinFluct.Linear.theorem1_di
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:36:18.667335+00:00
-- url     : https://prove2.me/theorems/24962a35-caff-4c22-be4f-bbb898e13fe0
-- title:
--   Theorem 1(d)–(i) — monotone values, differences and levels
-- statement:
--   For the zero-fixed-cost recursion started at $W_0=0$, both $W_n$ and $G_n$ are nonnegative and nondecreasing in stage number. Their forward differences are ordered, and the smallest minimizers $y_n^*(i)$ are nonincreasing in $n$. Below the smallest myopic level $y^+_{\min}$, the difference of $G_n$ equals the strictly negative difference of $G^+$. In particular,
--
--   $$0\le y^+_{\min}\le y_n^*(i),\qquad y_{n+1}^*(i)\le y_n^*(i).$$
--
--   The inequalities control the limit of the integer basestock levels.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 357, Theorem 1 (printed "Theorem 4"), parts (d)–(i)

import Mathlib
import Definitions.Def_SongZipkinFluct_Linear_Dynamics

namespace SongZipkinFluct.Linear

/-- Song and Zipkin (1993), Theorem 1(d)--(i), printed "Theorem 4",
p. 357. `K=0` and `W₀=0` are the subsection's choices. `ymin` is
the actual least member of the range of the myopic minimizer levels,
not an integer infimum with a default value. -/
theorem theorem1_di {I : Type*} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) (hA : M.Assumption1) :
    ∃ (ys : ℕ → I → ℤ) (yplus : I → ℤ) (ymin : ℤ),
      (∀ i : I, SmallestMinimizer (M.Gplus i) (yplus i)) ∧
      IsLeast (Set.range yplus) ymin ∧
      (∀ n : ℕ, 1 ≤ n → ∀ i : I,
        SmallestMinimizer (M.Glin n i) (ys n i)) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ i : I, ∀ x : ℤ,
        0 ≤ M.Wlin (n - 1) i x ∧
        M.Wlin (n - 1) i x ≤ M.Wlin n i x ∧
        0 ≤ Delta (M.Wlin (n - 1)) i x ∧
        Delta (M.Wlin (n - 1)) i x ≤ Delta (M.Wlin n) i x) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ i : I, ∀ y : ℤ,
        0 ≤ M.Glin n i y ∧
        M.Glin n i y ≤ M.Glin (n + 1) i y ∧
        Delta (M.Glin n) i y ≤ Delta (M.Glin (n + 1)) i y) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ i : I, ys (n + 1) i ≤ ys n i) ∧
      0 ≤ ymin ∧
      ∀ n : ℕ, 1 ≤ n → ∀ i : I,
        ymin ≤ ys n i ∧
        ∀ y : ℤ, y < ymin →
          Delta (M.Glin n) i y = Delta M.Gplus i y ∧
          Delta M.Gplus i y < 0 := by sorry

end SongZipkinFluct.Linear
