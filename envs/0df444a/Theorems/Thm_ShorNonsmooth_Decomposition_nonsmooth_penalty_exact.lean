-- Prove2me | Theorems.Thm_ShorNonsmooth_Decomposition_nonsmooth_penalty_exact
-- name    : ShorNonsmooth.Decomposition.nonsmooth_penalty_exact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T16:31:28.899978+00:00
-- url     : https://prove2.me/theorems/f7db871e-fe22-4ea5-89ff-ba910b0e18fa
-- title:
--   Theorem 4.2 — exactness of nonsmooth penalty functions with slopes above the Lagrange multipliers
-- statement:
--   Let $f_0, f_1, \dots, f_m$ be convex functions on $E_N$ and consider the convex program (4.178) $\min f_0(x)$ s.t. $f_i(x) \le 0$. Let $p_1,\dots,p_m$ be convex functions on $\mathbb{R}$ with $p_i(t) = 0$ for $t \le 0$ and $p_i(t) > 0$ for $t > 0$, let
--   $$
--   c_i = \lim_{t \to 0+} \frac{p_i(t)}{t},
--   $$
--   and let $x^*$ minimize the penalized function $S(x) = f_0(x) + \sum_{i=1}^m p_i[f_i(x)]$ over all $x$. Then:
--
--   1. if $x^*$ is a solution of (4.178), there is a Lagrange multiplier vector $\bar y$ of (4.178) with $c_i \ge \bar y_i$ for all $i$;
--   2. if $\bar y$ is a Lagrange multiplier vector of (4.178) and $c_i > \bar y_i$ for all $i$, then the set of minimum points of (4.178) equals the set of minimum points of $S$.
--
--   Part 2 is the exact-penalty principle: with slopes $c_i$ above the multipliers, e.g. $p_i(t) = c_i t^+$, one minimization of the nonsmooth function $S$ replaces the constrained problem.
--
--   **Formalization Note** The book's "where $\bar y$ is a Lagrange multiplier vector" is read existentially in part 1: the reading "for every multiplier vector" is false when multipliers are not unique (duplicate constraints give a counterexample). A multiplier vector is $\bar y \ge 0$ with $f_0 + \sum \bar y_i f_i \ge f^*$ everywhere, $f^*$ the finite optimal value. The limit $c_i$ is supplied as a hypothesis (it exists for every such $p_i$).
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 147, Theorem 4.2 (setting p. 146, formulas (4.178)–(4.179))

import Mathlib
import Definitions.Def_ShorNonsmooth_Decomposition_PenaltyDual

namespace ShorNonsmooth.Decomposition

open Filter Topology

/-- Shor (1985), **Theorem 4.2** (p. 147), for the convex program (4.178) `min f₀(x)` s.t. `f_i(x) ≤ 0` and
the penalized function (4.179) `S(x) = f₀(x) + Σ p_i[f_i(x)]` with nonsmooth penalty functions `p_i`
(convex, `0` on `t ≤ 0`, positive on `t > 0`), `c_i = lim_{t→0+} p_i(t)/t`, and a point `x*` minimizing
`S` over all `x` (standing assumption, p. 146):

1. (necessity) if `x*` is a solution of (4.178), then `c_i ≥ ȳ_i` for all `i` for some Lagrange
   multiplier vector `ȳ` of (4.178);
2. if `ȳ` is a Lagrange multiplier vector of (4.178) with `c_i > ȳ_i` for all `i`, then the sets of
   minimum points of (4.178) and of `S` are equal.

The book's "a Lagrange multiplier vector" is read existentially in (1) (the universal reading is false
when the multiplier is not unique). -/
theorem nonsmooth_penalty_exact {N m : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin N) → ℝ) (f : Fin m → EuclideanSpace ℝ (Fin N) → ℝ)
    (hf₀ : ConvexOn ℝ Set.univ f₀) (hf : ∀ i, ConvexOn ℝ Set.univ (f i))
    (p : Fin m → ℝ → ℝ) (hp : ∀ i, IsPenaltyFunction (p i))
    (c : Fin m → ℝ) (hc : ∀ i, Tendsto (fun t => p i t / t) (𝓝[>] 0) (𝓝 (c i)))
    (xstar : EuclideanSpace ℝ (Fin N)) (hxstar : ∀ x, penalized f₀ f p xstar ≤ penalized f₀ f p x) :
    (xstar ∈ solutionSet f₀ f →
        ∃ ybar : Fin m → ℝ, IsLagrangeMultiplierVector f₀ f ybar ∧ ∀ i, ybar i ≤ c i) ∧
      ∀ ybar : Fin m → ℝ, IsLagrangeMultiplierVector f₀ f ybar → (∀ i, ybar i < c i) →
        solutionSet f₀ f = {x | ∀ x', penalized f₀ f p x ≤ penalized f₀ f p x'} := by sorry

end ShorNonsmooth.Decomposition
