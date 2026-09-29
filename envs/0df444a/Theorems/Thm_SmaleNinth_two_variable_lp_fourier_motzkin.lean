-- Prove2me | Theorems.Thm_SmaleNinth_two_variable_lp_fourier_motzkin
-- name    : SmaleNinth.two_variable_lp_fourier_motzkin
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T01:43:01.910028+00:00
-- url     : https://prove2.me/theorems/09baf727-65f1-40cb-ac33-3fcb9b7f28c3
-- title:
--   Fourier-Motzkin elimination in two variables
-- statement:
--   Write the constraints of a two-variable system as $a_i x + b_i y \ge c_i$ for $i < m$, where $a_i = A_{i0}$ and $b_i = A_{i1}$. Then the system has a solution $(x,y) \in \mathbb{R}^2$ if and only if the following one-variable system in the unknown $t$ has a solution:
--
--   $$a_i t \ge c_i \quad (b_i = 0), \qquad (b_i a_j - b_j a_i)\, t \ \ge\ b_i c_j - b_j c_i \quad (b_i > 0 > b_j).$$
--
--   This is Fourier–Motzkin elimination of the variable $y$. In one direction, each inequality of the reduced system is a nonnegative combination of the original ones: the pair inequality is $(-b_j)$ times constraint $i$ plus $b_i$ times constraint $j$, in which the $y$ terms cancel. In the other direction, a solution $t$ of the reduced system is extended to a solution of the original one by choosing $y$ between the largest lower bound $\max_{b_i>0}(c_i - a_i t)/b_i$ and the smallest upper bound $\min_{b_j<0}(c_j - a_j t)/b_j$; the pair inequalities say exactly that every lower bound is at most every upper bound, and the degenerate cases where one or both families are empty are immediate.
--
--   The reduced system has at most $m + m^2/4$ inequalities in one variable, so the elimination turns a two-variable feasibility question into a one-variable one at quadratic cost. Combined with a one-variable decision procedure it gives a polynomial-time algorithm for two-variable linear programming in a machine model with indirect addressing, which is the first nontrivial case of the fixed-dimension results of Megiddo and Dyer. For the general problem the elimination is of no use, since eliminating $n$ variables in turn can square the number of constraints each time; that blow-up is precisely why Smale's ninth problem is not settled by this classical method.
-- source:
--   J. B. J. Fourier (1826); T. Motzkin, Beitraege zur Theorie der linearen Ungleichungen, Dissertation, Basel 1936. See A. Schrijver, Theory of Linear and Integer Programming, Wiley 1986, Section 12.2, and Bertsimas-Tsitsiklis, Introduction to Linear Optimization, Athena Scientific 1997, Section 2.8 (elimination of a variable from a system of linear inequalities).

import Definitions.Def_Polyhedron

/-!
Fourier-Motzkin elimination in two variables: feasibility of a two-variable
system is equivalent to feasibility of a one-variable system built from the
constraints with zero second coefficient and from the pairs of constraints
with opposite second coefficients.

Source: J. B. J. Fourier (1826) and T. Motzkin (1936); see A. Schrijver,
*Theory of Linear and Integer Programming*, Wiley 1986, Section 12.2, and
Bertsimas-Tsitsiklis, *Introduction to Linear Optimization*, Athena
Scientific 1997, Section 2.8.
-/

open Matrix LinearOptimization

/-- **Fourier-Motzkin elimination, two variables.** The system `Ax >= c` in two
variables is feasible if and only if the one-variable system obtained by
eliminating the second variable is feasible. -/

theorem SmaleNinth.two_variable_lp_fourier_motzkin {m : ℕ} (A : Matrix (Fin m) (Fin 2) ℝ)
    (c : Fin m → ℝ) :
    (polyhedron A c).Nonempty ↔
      ∃ t : ℝ,
        (∀ i : Fin m, A i 1 = 0 → c i ≤ A i 0 * t) ∧
        (∀ i j : Fin m, 0 < A i 1 → A j 1 < 0 →
          A i 1 * c j - A j 1 * c i ≤ (A i 1 * A j 0 - A j 1 * A i 0) * t) := by sorry
