-- Prove2me | Theorems.Thm_SmithHitAndRun_RandomDir_density_lower_bound
-- name    : SmithHitAndRun.RandomDir.density_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:37:54.56201+00:00
-- url     : https://prove2.me/theorems/6abe9037-56ca-48d7-a5ac-241adff6ebff
-- title:
--   Proof of Theorem 3 — $f(y\mid x)>\delta=2/dS_n(d)$ for all distinct $x,y\in S$
-- statement:
--   Let $n\ge2$, let $S\subseteq\mathbb R^n$ be open and bounded with diameter $d$, and let $f(y\mid x)=2/(S_n(r(x,y))\,\ell(x,y))$ be the Random Directions density. Then for all $x,y\in S$ with $x\ne y$,
--   $$f(y\mid x)>\delta=\frac{2}{d\,S_n(d)}.$$
--
--   Together with the density formula, this gives the uniform minorization $P(A\mid x)\ge\delta\,V(A)$ on $S$ needed by Doob's bound.
--
--   **Formalization Note** The paper's $d=\max_{x,y\in S}d(x,y)$ is taken to be the diameter of $S$, which bounds both $r(x,y)$ and the line-set length $\ell(x,y)$ for every region (for non-convex $S$ the maximal chord can be smaller than $r(x,y)$). The hypothesis $n\ge2$ is needed for the strict inequality: for $n=1$, $S_n(r)=2$ does not depend on $r$ and equality can hold. The statement excludes $y=x$, where $f$ is not meaningful.
-- source:
--   Smith, Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed over Bounded Regions, Oper. Res. 32(6) (1984), p. 1304, Proof of Theorem 3

import Mathlib
import Definitions.Def_SmithHitAndRun_RandomDir_RateConstants

open MeasureTheory

namespace SmithHitAndRun.RandomDir

/-- Smith 1984, p. 1304, proof of Theorem 3: for `n ≥ 2` and an open bounded region `S ⊆ ℝⁿ`,
`f(y | x) > δ = 2 / (d S_n(d))` for all distinct `x, y ∈ S`, where `d` is the diameter of `S`. -/
theorem density_lower_bound {n : ℕ} (hn : 2 ≤ n)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hSo : IsOpen S) (hSb : Bornology.IsBounded S)
    (x y : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    ENNReal.ofReal (deltaConst S) < rdDensity S x y := by sorry

end SmithHitAndRun.RandomDir
