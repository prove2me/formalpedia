-- Prove2me | Theorems.Thm_ShorNonsmooth_Decomposition_dual_bound_le_optimum
-- name    : ShorNonsmooth.Decomposition.dual_bound_le_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T16:36:01.757196+00:00
-- url     : https://prove2.me/theorems/da5db52f-1cfc-4b4e-9255-f1cf7b0357e8
-- title:
--   Theorem 4.3 — the Lagrangian dual bound $Q = \max_{u \ge 0} \Phi(u)$ does not exceed $f^*$
-- statement:
--   Consider the problem (4.185)–(4.186): $\min f_0(x)$ over $x \in X \subseteq E_N$ subject to $f_i(x) \le 0$, $i = 1,\dots,m$, where $X$ is compact. Let
--   $$
--   \Phi(u) = \min_{x \in X}\Big[f_0(x) + \sum_{i=1}^m u_i f_i(x)\Big] \qquad (4.187)
--   $$
--   and $Q = \max_{u \ge 0} \Phi(u)$. If $f^*$ is the optimum value of (4.185)–(4.186), then
--   $$
--   Q \le f^* .
--   $$
--   $Q$ is the lower estimate of $f^*$ used in branch-and-bound methods for discrete and mixed discrete-continuous programs (where $X$ is partially discrete); computing it is a nonsmooth concave maximization.
--
--   **Formalization Note** The optimum $f^*$ is attained (a least element of $f_0$ on the feasible part of $X$), and $Q$ is assumed to be attained, as the book's "max" presupposes. The minimum in (4.187) is assumed to be attained for every $u \ge 0$, as the book's "min" presupposes (no continuity is assumed; for a partially discrete $X$ the functions need not be continuous). $X$ is an arbitrary compact set; its partial discreteness plays no role.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 148, Theorem 4.3 (formulas (4.185)–(4.187))

import Mathlib
import Definitions.Def_ShorNonsmooth_Decomposition_PenaltyDual

namespace ShorNonsmooth.Decomposition

/-- Shor (1985), **Theorem 4.3** (p. 148): for problem (4.185)–(4.186), `min f₀(x)` over `x ∈ X ⊂ E_N`
subject to `f_i(x) ≤ 0`, with `X` compact, let `Φ(u) = min_{x ∈ X}[f₀(x) + Σ u_i f_i(x)]` (4.187) and
`Q = max_{u ≥ 0} Φ(u)`. If `f*` is the optimum value of (4.185)–(4.186), then `Q ≤ f*`.
The minimum in (4.187) is assumed to be attained for every `u ≥ 0` (the book writes `min`), the optimum
`f*` is attained, and `Q` is assumed to be attained, as the book's `max` presupposes. -/
theorem dual_bound_le_optimum {N m : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin N))) (hX : IsCompact X)
    (f₀ : EuclideanSpace ℝ (Fin N) → ℝ) (f : Fin m → EuclideanSpace ℝ (Fin N) → ℝ)
    (hmin : ∀ u : Fin m → ℝ, (∀ i, 0 ≤ u i) →
      ∃ x ∈ X, ∀ x' ∈ X, f₀ x + ∑ i, u i * f i x ≤ f₀ x' + ∑ i, u i * f i x')
    (fstar : ℝ) (hfstar : IsLeast (f₀ '' (X ∩ feasibleSet f)) fstar)
    (Q : ℝ) (hQ : IsGreatest (dualFn X f₀ f '' {u | ∀ i, 0 ≤ u i}) Q) :
    Q ≤ fstar := by sorry

end ShorNonsmooth.Decomposition
