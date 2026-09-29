-- Prove2me | Theorems.Thm_SmaleNinth_lp_complementary_slackness
-- name    : SmaleNinth.lp_complementary_slackness
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T02:33:08.743013+00:00
-- url     : https://prove2.me/theorems/02d4ff4e-78ec-4a94-9935-bbab727fdaa1
-- title:
--   Complementary slackness
-- statement:
--   Let $x$ satisfy $Ax \ge b$ and let $y \ge 0$ satisfy $A^{\mathsf T}y = c$, so that $x$ is primal feasible and $y$ dual feasible for
--   $$\min\ c^{\mathsf T}x \ \text{ s.t. } Ax \ge b, \qquad \max\ b^{\mathsf T}y \ \text{ s.t. } y \ge 0,\ A^{\mathsf T}y = c .$$
--   Then their objective values agree if and only if
--
--   $$y_i \bigl((Ax)_i - b_i\bigr) = 0 \qquad \text{for every } i,$$
--
--   that is, no constraint is simultaneously slack and carrying a positive dual variable.
--
--   The identity behind it is that the duality gap decomposes into the individual slacks:
--   $$c^{\mathsf T}x - b^{\mathsf T}y = \sum_i y_i\bigl((Ax)_i - b_i\bigr),$$
--   obtained by substituting $c = A^{\mathsf T}y$ and exchanging the order of summation. Every summand is nonnegative, being a product of $y_i \ge 0$ with a nonnegative slack, so the sum vanishes precisely when each term does. By weak duality the equal value is then the common optimum, so complementary slackness is the pointwise optimality criterion for a primal-dual pair.
--
--   This is the condition that primal-dual and interior-point algorithms drive to zero, and it is the certificate an algorithm checks when it stops. Together with `SmaleNinth.lp_strong_duality`, which guarantees that such a pair exists whenever the primal is feasible and bounded, it says that optimality in linear programming is witnessed by a finite, locally checkable condition rather than by a comparison against all feasible points.
-- source:
--   D. Gale, H. W. Kuhn, A. W. Tucker, Linear programming and the theory of games, in Activity Analysis of Production and Allocation, Wiley 1951; see Bertsimas-Tsitsiklis, Introduction to Linear Optimization, Athena Scientific 1997, Theorem 4.5, and A. Schrijver, Theory of Linear and Integer Programming, Wiley 1986, Section 7.9.

import Definitions.Def_Polyhedron

/-!
Complementary slackness for the inequality form of linear programming: a
feasible primal solution and a feasible dual solution have equal objective
values exactly when every dual variable vanishes on a slack constraint.

Source: G. B. Dantzig, D. Gale, H. W. Kuhn and A. W. Tucker (1951); see
Bertsimas-Tsitsiklis, *Introduction to Linear Optimization*, Athena Scientific
1997, Theorem 4.5, and A. Schrijver, *Theory of Linear and Integer
Programming*, Wiley 1986, Section 7.9.
-/

open Matrix LinearOptimization

/-- **Complementary slackness.** For a feasible `x` and a dual feasible `y`,
the objective values agree if and only if `yᵢ = 0` whenever the `i`-th
constraint is slack. -/

theorem SmaleNinth.lp_complementary_slackness {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) {x : Fin n → ℝ} {y : Fin m → ℝ}
    (hx : x ∈ polyhedron A b) (hy0 : ∀ i, 0 ≤ y i) (hyA : ∀ k, ∑ i, y i * A i k = c k) :
    (∑ k, c k * x k = ∑ i, y i * b i) ↔ ∀ i, y i * ((A.mulVec x) i - b i) = 0 := by sorry
