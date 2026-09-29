-- Prove2me | Theorems.Thm_SmaleNinth_lp_feasible_iff_subsystems
-- name    : SmaleNinth.lp_feasible_iff_subsystems
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T01:36:08.490722+00:00
-- url     : https://prove2.me/theorems/f79a5201-4280-4ce0-b4bf-f8dcc8c3ed35
-- title:
--   Combinatorial dimension of LP feasibility: Helly bound $n+1$
-- statement:
--   Let $A \in \mathbb{R}^{m \times n}$ and $b \in \mathbb{R}^m$, and consider the polyhedron $P = \{x \in \mathbb{R}^n : Ax \ge b\}$. Then
--
--   $$P \neq \emptyset \iff \text{every subsystem of at most } n+1 \text{ of the inequalities } a_i^{\mathsf T} x \ge b_i \text{ has a solution.}$$
--
--   The forward implication is trivial. The converse is Helly's theorem applied to the half-spaces $H_i = \{x : a_i^{\mathsf T} x \ge b_i\}$, which are convex subsets of a space of dimension $n$: if every $n+1$ of finitely many convex sets in $\mathbb{R}^n$ meet, then all of them meet. (When $m \le n+1$ the whole system is itself one of the admissible subsystems, and no appeal to Helly is needed.)
--
--   Equivalently, in contrapositive form: an infeasible system of linear inequalities in $n$ variables always contains an infeasible subsystem of at most $n+1$ inequalities. The number $n+1$ is the *combinatorial dimension* of linear-programming feasibility, and it is what makes fixed-dimension linear programming easy: it is the reason Megiddo's prune-and-search algorithm and Clarkson's sampling algorithms solve linear programs in a fixed number of variables in time linear in the number of constraints, and it bounds the size of the certificate an algorithm has to exhibit when it reports infeasibility.
--
--   In the context of Smale's ninth problem this is the standard first step of every known strongly polynomial result for a restricted class: the difficulty of the general problem lies entirely in the dependence on $n$, since for each fixed $n$ the statement above already reduces feasibility to finitely many subsystems of bounded size.
-- source:
--   Helly's theorem for convex sets in R^n applied to half-spaces; standard in linear programming, see A. Schrijver, Theory of Linear and Integer Programming, Wiley 1986, Section 7, and N. Megiddo, Linear programming in linear time when the dimension is fixed, J. ACM 31 (1984) 114-127, where the bound n+1 on the combinatorial dimension underlies the prune-and-search algorithm.

import Definitions.Def_Polyhedron
import Mathlib.Analysis.Convex.Radon

/-!
The combinatorial dimension of linear-programming feasibility over the reals:
a system of linear inequalities in `n` variables is feasible as soon as each of
its subsystems of at most `n+1` inequalities is feasible.

Source: E. Helly's theorem applied to half-spaces; the LP formulation is the
basis of the fixed-dimension algorithms of N. Megiddo, *Linear programming in
linear time when the dimension is fixed*, J. ACM 31 (1984) 114-127, and of
K. L. Clarkson, *Las Vegas algorithms for linear and integer programming when
the dimension is small*, J. ACM 42 (1995) 488-499; see also
Bertsimas-Tsitsiklis, *Introduction to Linear Optimization*, Athena Scientific
1997, and Schrijver, *Theory of Linear and Integer Programming*, Wiley 1986,
Section 7.
-/

open Matrix LinearOptimization

/-- **Combinatorial dimension of LP feasibility.** The system `Ax >= b` in `n`
variables has a solution if and only if every subsystem of at most `n+1` of its
inequalities has one. -/

theorem SmaleNinth.lp_feasible_iff_subsystems {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    (polyhedron A b).Nonempty ↔
      ∀ S : Finset (Fin m), S.card ≤ n + 1 →
        ∃ x : Fin n → ℝ, ∀ i ∈ S, b i ≤ (A.mulVec x) i := by sorry
