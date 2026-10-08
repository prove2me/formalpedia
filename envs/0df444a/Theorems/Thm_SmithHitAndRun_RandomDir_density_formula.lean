-- Prove2me | Theorems.Thm_SmithHitAndRun_RandomDir_density_formula
-- name    : SmithHitAndRun.RandomDir.density_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:37:34.32922+00:00
-- url     : https://prove2.me/theorems/d6d31c2d-9225-4a64-b1c6-61be6b42d1e4
-- title:
--   Proof of Theorem 3 — the Random Directions kernel has density $f(y\mid x)=2/S_n(r(x,y))\,\ell(x,y)$
-- statement:
--   Let $n\ge1$, let $S\subseteq\mathbb R^n$ be open and bounded, and let $x\in S$. For $y\ne x$ write $r(x,y)=\|y-x\|$, let $\ell(x,y)$ be the length of the line set of $S$ through $x$ in direction $(y-x)/\|y-x\|$, and let $S_n(r)=nV_n(1)r^{n-1}$ be the surface area of a sphere of radius $r$. Then the Random Directions transition probability is absolutely continuous on $S$ with density
--   $$f(y\mid x)=\frac{2}{S_n(r(x,y))\,\ell(x,y)},$$
--   that is, for every measurable $A\subseteq S$,
--   $$P(A\mid x)=\int_A f(y\mid x)\,\mathrm dy.$$
--
--   This identifies the transition density of the algorithm explicitly; it is the input to the minorization in the proof of Theorem 3.
--
--   **Formalization Note** The paper writes $d(x,y)$, the diameter of $S$ along the ray, in place of $\ell(x,y)$; the two agree for convex $S$, and $\ell$ is what the algorithm actually uses for any open $S$. The integral is a Lebesgue integral in $[0,\infty]$; the value of $f$ at $y=x$ does not matter.
-- source:
--   Smith, Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed over Bounded Regions, Oper. Res. 32(6) (1984), p. 1304, Proof of Theorem 3

import Mathlib
import Definitions.Def_SmithHitAndRun_RandomDir_RandomDirectionsKernel
import Definitions.Def_SmithHitAndRun_RandomDir_RateConstants

open MeasureTheory ProbabilityTheory

namespace SmithHitAndRun.RandomDir

/-- Smith 1984, p. 1304, proof of Theorem 3: for an open bounded region `S ⊆ ℝⁿ` and `x ∈ S`, the
Random Directions transition probability has the density
`f(y | x) = 2 / (S_n(r(x,y)) ℓ(x,y))` with respect to Lebesgue measure on `S`:
`P(A | x) = ∫_A f(y | x) dy` for every measurable `A ⊆ S`. -/
theorem density_formula {n : ℕ} (hn : 1 ≤ n)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hSo : IsOpen S) (hSb : Bornology.IsBounded S)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S)
    (A : Set (EuclideanSpace ℝ (Fin n))) (hA : MeasurableSet A) (hAS : A ⊆ S) :
    rdKernel S x A = ∫⁻ y in A, rdDensity S x y := by sorry

end SmithHitAndRun.RandomDir
