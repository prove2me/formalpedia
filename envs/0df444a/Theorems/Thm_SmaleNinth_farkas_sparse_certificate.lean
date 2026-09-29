-- Prove2me | Theorems.Thm_SmaleNinth_farkas_sparse_certificate
-- name    : SmaleNinth.farkas_sparse_certificate
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T02:29:23.617883+00:00
-- url     : https://prove2.me/theorems/65bf1f49-a484-42b0-9ae3-7624e71c85a7
-- title:
--   Farkas certificates of support at most $n+1$
-- statement:
--   If the system $Ax \ge b$ has no solution in $\mathbb{R}^n$, then it has a Farkas certificate of infeasibility supported on at most $n+1$ of its rows: a vector $y \ge 0$ with
--
--   $$y^{\mathsf T} A = 0, \qquad y^{\mathsf T} b > 0, \qquad |\{i : y_i \neq 0\}| \le n+1 .$$
--
--   The bound on the support does not depend on the number of inequalities. It follows by combining two facts. Helly's theorem says that an infeasible system always contains an infeasible subsystem of at most $n+1$ inequalities, since the half-spaces are convex subsets of a space of dimension $n$. Farkas' lemma applied to that subsystem gives multipliers for its rows, which extend by zero to multipliers for the whole system.
--
--   The statement makes the cost of certifying a negative answer independent of the size of the instance: a refutation names at most $n+1$ constraints and the coefficients that combine them into the contradiction $0 \ge \varepsilon > 0$. Together with the dual certificate of optimality from linear programming duality, this is the sense in which linear programming has short proofs for both answers, and it is the invariant on which the sampling algorithms for fixed and small dimension are built. For Smale's ninth problem it isolates the remaining difficulty as one of search rather than of verification: what is missing is not a small certificate but a way to find one using a number of arithmetic operations polynomial in the number of constraints and variables.
-- source:
--   Helly's theorem for the half-spaces of the system together with Farkas' lemma; see A. Schrijver, Theory of Linear and Integer Programming, Wiley 1986, Sections 7.1-7.2, and K. L. Clarkson, Las Vegas algorithms for linear and integer programming when the dimension is small, J. ACM 42 (1995) 488-499, where the bound n+1 on the combinatorial dimension plays the same role.

import Definitions.Def_Polyhedron

/-!
Infeasibility certificates of bounded support: an infeasible system of linear
inequalities in `n` variables carries a Farkas certificate with at most `n+1`
nonzero multipliers.

Source: Helly's theorem (in the form
`SmaleNinth.lp_feasible_iff_subsystems`) combined with Farkas' lemma
(`SmaleNinth.farkas_lemma`); see A. Schrijver, *Theory of Linear and Integer
Programming*, Wiley 1986, Sections 7.1 and 7.2, and the discussion of
combinatorial dimension in K. L. Clarkson, *Las Vegas algorithms for linear and
integer programming when the dimension is small*, J. ACM 42 (1995) 488-499.
-/

open Matrix LinearOptimization

/-- **Sparse Farkas certificate.** An infeasible system `Ax >= b` in `n`
variables has a nonnegative combination of its rows witnessing infeasibility
with at most `n+1` nonzero coefficients. -/

theorem SmaleNinth.farkas_sparse_certificate {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (hinf : ¬ (polyhedron A b).Nonempty) :
    ∃ y : Fin m → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ k, ∑ i, y i * A i k = 0) ∧ 0 < ∑ i, y i * b i ∧
      (Finset.univ.filter (fun i => y i ≠ 0)).card ≤ n + 1 := by sorry
