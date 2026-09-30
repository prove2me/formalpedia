-- Prove2me | Theorems.Thm_Wets1974_Feasibility_K2_closed_convex_polyhedral
-- name    : Wets1974.Feasibility.K2_closed_convex_polyhedral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:32:56.059984+00:00
-- url     : https://prove2.me/theorems/90574ca9-1a1d-49c7-b0ba-ad9381feacac
-- title:
--   Theorem 4.7 — $K_2$ is closed and convex, and polyhedral when $\operatorname{pos}(\tilde\Xi_{p,T})$ is a polyhedral cone
-- statement:
--   Let $W$ be a fixed $\bar m \times \bar n$ matrix, $\mu$ the (probability) law of $\xi = (c, q, p, T)$, $\tilde\Xi_{p,T}$ the support of the marginal law of $(p,T)$, and
--
--   $$
--   K_2 = \{x \in \mathbb{R}^n \mid p - Tx \in \operatorname{pos} W \text{ for all } (p,T) \in \tilde\Xi_{p,T}\}.
--   $$
--
--   Then:
--
--   1. $K_2$ is a closed convex subset of $\mathbb{R}^n$;
--   2. if the closed positive hull $\operatorname{pos}(\tilde\Xi_{p,T})$ (the closure of the set of nonnegative linear combinations of points of $\tilde\Xi_{p,T}$) is a convex polyhedral cone, then $K_2$ is a convex polyhedron, i.e. $K_2 = \{x \mid Gx \ge \alpha\}$ for some finite system of linear inequalities.
--
--   No moment condition on $\xi$ is needed. Part 1 says the induced feasibility region is always well behaved; part 2 gives a checkable condition, on the distribution of $(p, T)$ alone, under which it is described by finitely many linear constraints.
--
--   **Formalization Note.** A convex polyhedral cone is taken to be the set of nonnegative combinations of finitely many vectors of $(p,T)$-space $\mathbb{R}^{\bar m} \times \mathbb{R}^{\bar m \times n}$; a convex polyhedron is the solution set of finitely many weak linear inequalities (the empty set and $\mathbb{R}^n$ included). The number of inequalities is an existentially quantified natural number.
-- source:
--   Wets, Stochastic Programs with Fixed Recourse: The Equivalent Deterministic Program, SIAM Review 16(3), 1974, p. 317, Theorem 4.7

import Mathlib
import Definitions.Def_Wets1974_Feasibility_Model

namespace Wets1974.Feasibility

open MeasureTheory

/-- Theorem 4.7, p. 317: `K₂` is a closed convex subset of `ℝⁿ`; moreover, if the closed
positive hull `pos(Ξ̃_{p,T})` is a convex polyhedral cone, then `K₂` is a convex polyhedron. -/
theorem K2_closed_convex_polyhedral {n nb mb : ℕ} (μ : Measure (DataSpace n nb mb))
    [IsProbabilityMeasure μ] (W : Matrix (Fin mb) (Fin nb) ℝ) :
    (IsClosed (K2 μ W) ∧ Convex ℝ (K2 μ W)) ∧
      (IsPolyhedralCone (closedPosHull (suppPT μ)) → IsPolyhedron (K2 μ W)) := by sorry

end Wets1974.Feasibility
