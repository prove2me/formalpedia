-- Prove2me | Theorems.Thm_SmaleNinth_lp_strong_duality
-- name    : SmaleNinth.lp_strong_duality
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T02:03:39.203215+00:00
-- url     : https://prove2.me/theorems/35a41d44-2ae1-40cb-845d-817314415fb8
-- title:
--   Strong duality for linear programming
-- statement:
--   Consider the linear program
--   $$\min\ c^{\mathsf T} x \quad \text{subject to } Ax \ge b, \qquad A \in \mathbb{R}^{m\times n},\ b \in \mathbb{R}^m,\ c \in \mathbb{R}^n,$$
--   and its dual
--   $$\max\ b^{\mathsf T} y \quad \text{subject to } y \ge 0,\ A^{\mathsf T} y = c .$$
--
--   If the primal is feasible and its objective is bounded below on the feasible set, then there exist a feasible $x$ and a dual feasible $y$ with
--   $$c^{\mathsf T} x = b^{\mathsf T} y,$$
--   and $x$ minimises the objective over the whole feasible set. In particular the primal optimum is attained, the dual is feasible, and the two optimal values coincide; weak duality, $b^{\mathsf T} y \le c^{\mathsf T} x$ for every feasible pair, shows that $y$ is then dual optimal as well.
--
--   Strong duality is the structural backbone of linear programming. It certifies optimality by a pair rather than by a search, it is what makes the simplex method's termination criterion sound, and it is the source of the complementary slackness conditions on which primal-dual and interior-point algorithms are built. For Smale's ninth problem it says that an optimal solution always comes with a checkable proof of optimality of the same size, so the difficulty is confined to producing the pair with a number of arithmetic operations polynomial in $m$ and $n$.
--
--   *Formalization note.* The proof is the classical derivation from Farkas' lemma. Boundedness of the objective rules out a feasible direction of descent and therefore forces the dual to be feasible. The primal-dual pair is then obtained by applying Farkas to the combined system in the variables $(x,y)$ consisting of primal feasibility, dual feasibility and the coupling inequality $c^{\mathsf T} x \le b^{\mathsf T} y$: an infeasibility certificate for that system has a multiplier on the coupling row which is either positive, in which case it yields a feasible pair violating weak duality, or zero, in which case it contradicts feasibility of the primal and of the dual.
-- source:
--   D. Gale, H. W. Kuhn, A. W. Tucker, Linear programming and the theory of games, in Activity Analysis of Production and Allocation, Wiley 1951; see A. Schrijver, Theory of Linear and Integer Programming, Wiley 1986, Corollary 7.1g (duality for the form Ax >= b), and Bertsimas-Tsitsiklis, Introduction to Linear Optimization, Athena Scientific 1997, Theorem 4.4.

import Definitions.Def_Polyhedron

/-!
Strong duality for linear programming in the inequality form: if the primal
program is feasible and its objective is bounded below on the feasible set,
then the optimum is attained and equals the optimum of the dual program.

Source: J. von Neumann (1947), G. B. Dantzig, D. Gale, H. W. Kuhn and
A. W. Tucker (1951); see A. Schrijver, *Theory of Linear and Integer
Programming*, Wiley 1986, Corollary 7.1g, and Bertsimas-Tsitsiklis,
*Introduction to Linear Optimization*, Athena Scientific 1997, Theorem 4.4.
-/

open Matrix LinearOptimization

/-- **Strong duality.** If `min c'x` over `Ax >= b` is feasible and bounded
below, then there are a primal optimal `x` and a dual feasible `y >= 0` with
`y'A = c'` whose objective values agree. -/

theorem SmaleNinth.lp_strong_duality {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hfeas : (polyhedron A b).Nonempty)
    (hbdd : ∃ v : ℝ, ∀ x ∈ polyhedron A b, v ≤ ∑ k, c k * x k) :
    ∃ (x : Fin n → ℝ) (y : Fin m → ℝ),
      x ∈ polyhedron A b ∧ (∀ i, 0 ≤ y i) ∧ (∀ k, ∑ i, y i * A i k = c k) ∧
      (∑ k, c k * x k = ∑ i, y i * b i) ∧
      (∀ x' ∈ polyhedron A b, ∑ k, c k * x k ≤ ∑ k, c k * x' k) := by sorry
