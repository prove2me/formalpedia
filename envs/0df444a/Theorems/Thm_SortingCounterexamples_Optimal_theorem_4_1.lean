-- Prove2me | Theorems.Thm_SortingCounterexamples_Optimal_theorem_4_1
-- name    : SortingCounterexamples.Optimal.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:19.833671+00:00
-- url     : https://prove2.me/theorems/dee98612-2a51-492b-9f6a-5740e163eb5d
-- title:
--   Theorem 4.1 (Grünbaum's inequality) — every halfspace containing the barycenter of a log-concave density has probability $\ge 1/e$
-- statement:
--   Let $p:\mathbb R^n\to\mathbb R$ be a log-concave probability density: $p\ge0$,
--   $$p(\lambda x+(1-\lambda)y)\ \ge\ p(x)^{\lambda}p(y)^{1-\lambda}\qquad(x,y\in\mathbb R^n,\ \lambda\in[0,1]),$$
--   and $\int_{\mathbb R^n}p=1$. Let $c=\int_{\mathbb R^n}x\,p(x)\,dx$ be its barycenter. Then every halfspace $H=\{x:\langle a,x\rangle\ge b\}$ with $a\ne0$ and $c\in H$ satisfies
--   $$\Pr_{X\sim p}[X\in H]=\int_H p(x)\,dx\ \ge\ \frac1e .$$
--
--   For the uniform density on a convex body this is Grünbaum's classical inequality; the general log-concave form is the one needed for the non-uniform weights of the upper bound.
--
--   **Formalization Note** The Bochner condition $\int p=1$ forces integrability, including almost-everywhere measurability; pointwise Borel measurability is not asserted. This suffices for the Lebesgue density and its probabilities. The barycenter's integrand is integrable for every log-concave probability density (exponential tails), so the barycenter is the true mean. Halfspaces are closed; an open halfspace containing $c$ differs from its closure by a hyperplane, which has probability $0$ under a density.
--
--   Differences from the source:
--   - encoding: every halfspace H containing c (open or closed) → closed halfspaces {x : b ≤ ⟪a, x⟫} with a ≠ 0; reason: an open halfspace containing c has the same probability as its closure, which also contains c, since hyperplanes are Lebesgue-null
-- source:
--   Noga Alon, Shay Moran, Shlomo Moran, STOC 2027 submission #549 (October 2026), printed p. 15 / PDF p. 16, Theorem 4.1 and the definition of log-concave density displayed above it

import Mathlib
import Definitions.Def_LogConcaveOn

open MeasureTheory

namespace SortingCounterexamples.Optimal

/-- Theorem 4.1 (Grünbaum's inequality for log-concave densities): a closed halfspace
`{x : b ≤ ⟪a, x⟫}` (`a ≠ 0`) containing the barycenter of a log-concave probability density
`p` on `ℝ^n` has probability at least `1/e`. -/
theorem theorem_4_1 {n : ℕ} (p : (Fin n → ℝ) → ℝ)
    (hp : ConvexOptimization.LogConcaveOn Set.univ p) (hmass : ∫ x, p x = 1)
    (a : Fin n → ℝ) (ha : a ≠ 0) (b : ℝ)
    (hc : b ≤ ∑ i, a i * (∫ x, p x • x) i) :
    Real.exp (-1) ≤ ∫ x in {x : Fin n → ℝ | b ≤ ∑ i, a i * x i}, p x := by sorry

end SortingCounterexamples.Optimal
