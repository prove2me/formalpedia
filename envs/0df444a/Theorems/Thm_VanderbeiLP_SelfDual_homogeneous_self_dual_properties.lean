-- Prove2me | Theorems.Thm_VanderbeiLP_SelfDual_homogeneous_self_dual_properties
-- name    : VanderbeiLP.SelfDual.homogeneous_self_dual_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T13:53:08.263148+00:00
-- url     : https://prove2.me/theorems/912a464c-f97a-4fe9-b7aa-57f5bc35fde9
-- title:
--   Theorem 22.1 — basic properties of homogeneous self-dual problems
-- statement:
--   Let $n \ge 2$ and let $A$ be a real skew-symmetric $n \times n$ matrix ($A = -A^T$). Consider the homogeneous self-dual problem (22.4)
--
--   $$\text{maximize } 0 \quad \text{subject to } Ax + z = 0,\quad x, z \ge 0.$$
--
--   Then:
--
--   1. (22.4) has feasible solutions, and every feasible solution is optimal;
--   2. the set of feasible solutions has empty interior: there is no feasible $(x, z)$ with $x > 0$ and $z > 0$. In fact, every feasible $(x, z)$ satisfies
--   $$z^T x = 0.$$
--
--   Part (2) says that a homogeneous self-dual problem has no central path, which is why the algorithm of §22.2 works with infeasible iterates.
--
--   **Formalization Note** "Empty interior" is read as in Chapter 17: no feasible point with every component of $x$ and $z$ strictly positive (the topological interior in $\mathbb{R}^{2n}$ is empty for trivial reasons, since the feasible set lies in the subspace $Ax + z = 0$). Optimality is optimality for the zero objective $0^Tx$. The hypothesis $n \ge 2$ is the standing assumption of §22.2 (p. 325).
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 325, Theorem 22.1 (PDF p. 331); standing assumptions n ≥ 2, A = −Aᵀ on p. 325

import Mathlib
import Definitions.Def_VanderbeiLP_SelfDual_HomogeneousSelfDual

open Matrix

namespace VanderbeiLP.SelfDual

/-- Theorem 22.1 (Vanderbei, p. 325). For the homogeneous self-dual problem (22.4) with
skew-symmetric `A` (`n ≥ 2`, the standing assumption of §22.2):
(1) it has feasible solutions and every feasible solution is optimal;
(2) no feasible solution has `x > 0` and `z > 0` (the feasible set has empty interior);
in fact every feasible `(x, z)` has `zᵀx = 0`. -/
theorem homogeneous_self_dual_properties {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSkewSymmetric A) :
    ((∃ x z : Fin n → ℝ, SelfDualFeasible A x z) ∧
      ∀ x z : Fin n → ℝ, SelfDualFeasible A x z → SelfDualOptimal A x z) ∧
    ((¬ ∃ x z : Fin n → ℝ, SelfDualFeasible A x z ∧ (∀ j, 0 < x j) ∧ ∀ j, 0 < z j) ∧
      ∀ x z : Fin n → ℝ, SelfDualFeasible A x z → z ⬝ᵥ x = 0) := by sorry

end VanderbeiLP.SelfDual
