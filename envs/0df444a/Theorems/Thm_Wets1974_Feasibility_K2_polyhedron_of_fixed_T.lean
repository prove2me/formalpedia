-- Prove2me | Theorems.Thm_Wets1974_Feasibility_K2_polyhedron_of_fixed_T
-- name    : Wets1974.Feasibility.K2_polyhedron_of_fixed_T
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:33:22.384478+00:00
-- url     : https://prove2.me/theorems/7ef65f02-75a7-44b5-a2b6-0722f5be6bf4
-- title:
--   Theorem 4.10 — when $T$ is fixed, the induced feasibility region $K_2$ is a closed convex polyhedron
-- statement:
--   Consider a stochastic program with fixed recourse (2.1): a fixed $\bar m \times \bar n$ recourse matrix $W$ of full row rank and random data $\xi = (c, q, p, T)$ with law $\mu$, a probability measure. Let $\tilde\Xi_{p,T}$ be the support of the marginal law of $(p, T)$ and
--
--   $$
--   K_2 = \{x \in \mathbb{R}^n \mid p - Tx \in \operatorname{pos} W \text{ for all } (p,T) \in \tilde\Xi_{p,T}\}, \qquad \operatorname{pos} W = \{Wy \mid y \ge 0\},
--   $$
--
--   the set of constraints induced on the first-stage decision $x$ (Corollary 4.5). Suppose that
--
--   1. $T$ is fixed: there is a matrix $T_0$ with $T(\xi) = T_0$ with probability one;
--   2. $\xi$ satisfies the weak covariance condition of Definition 2.2.
--
--   Then $K_2$ is a closed convex polyhedron: there are finitely many linear inequalities $Gx \ge \alpha$ with
--
--   $$
--   K_2 = \{x \mid Gx \ge \alpha\}.
--   $$
--
--   This is the result that makes the deterministic equivalent program of a stochastic program with fixed recourse and fixed technology matrix a program with finitely many deterministic linear constraints, even when the right-hand side $p(\xi)$ has an unbounded continuous distribution. The set $K_2$ may be empty.
--
--   **Formalization Note.** "$T$ is fixed" is read as "$T(\xi)$ is almost surely equal to one matrix $T_0$", which is weaker than pointwise constancy and so makes the theorem stronger. Full row rank of $W$ is the paper's standing assumption (p. 312); it is not needed for this conclusion. "Convex polyhedron" is the solution set of finitely many weak linear inequalities, the form (4.12) the paper's proof produces, and it includes $\emptyset$ and $\mathbb{R}^n$. Closedness and convexity are stated as separate conjuncts to mirror the paper's wording.
-- source:
--   Wets, Stochastic Programs with Fixed Recourse: The Equivalent Deterministic Program, SIAM Review 16(3), 1974, p. 318, Theorem 4.10 (form (4.12)); K₂ from Corollary 4.5, p. 316

import Mathlib
import Definitions.Def_Wets1974_Feasibility_Model

namespace Wets1974.Feasibility

open MeasureTheory

/-- Theorem 4.10, p. 318: if `T` is fixed in the stochastic program (2.1) and `ξ` satisfies a
weak covariance condition (with `W` of full row rank, the standing assumption of p. 312), then
`K₂` is a closed convex polyhedron. -/
theorem K2_polyhedron_of_fixed_T {n nb mb : ℕ} (μ : Measure (DataSpace n nb mb))
    [IsProbabilityMeasure μ] (W : Matrix (Fin mb) (Fin nb) ℝ)
    (hW : W.rank = mb) (hcov : WeakCovariance μ) (hT : TFixed μ) :
    IsClosed (K2 μ W) ∧ Convex ℝ (K2 μ W) ∧ IsPolyhedron (K2 μ W) := by sorry

end Wets1974.Feasibility
