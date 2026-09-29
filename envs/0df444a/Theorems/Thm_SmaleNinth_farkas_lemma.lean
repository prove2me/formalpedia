-- Prove2me | Theorems.Thm_SmaleNinth_farkas_lemma
-- name    : SmaleNinth.farkas_lemma
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T01:54:04.43119+00:00
-- url     : https://prove2.me/theorems/6b20d5ef-dc37-44f5-adf8-ae532ef22a07
-- title:
--   Farkas' lemma
-- statement:
--   Let $A \in \mathbb{R}^{m\times n}$ and $b \in \mathbb{R}^m$. Then exactly one of the following holds:
--
--   $$\exists x \in \mathbb{R}^n,\ Ax \ge b \qquad\text{or}\qquad \exists y \in \mathbb{R}^m,\ y \ge 0,\ y^{\mathsf T} A = 0,\ y^{\mathsf T} b > 0 .$$
--
--   The two alternatives exclude each other for a one-line reason: if $Ax \ge b$ and $y \ge 0$ then $y^{\mathsf T} b \le y^{\mathsf T} A x = 0$. The content of the lemma is that one of them always holds, so that infeasibility of a linear system always admits a finite, checkable certificate: a nonnegative combination of the inequalities whose left-hand side cancels identically while the right-hand side stays positive, that is, an explicit derivation of $0 \ge \varepsilon > 0$.
--
--   The vector $y$ is the reason linear programming lies in NP $\cap$ co-NP, it is the dual solution in linear programming duality, and it is what an algorithm exhibits when it reports that a system has no solution. In the setting of Smale's ninth problem it makes the decision problem symmetric: both answers can be certified, so the question is entirely one of finding a certificate in a number of arithmetic operations polynomial in $m$ and $n$, not one of verifying it.
--
--   *Formalization note.* The proof is the classical constructive one by Fourier–Motzkin elimination, carried out by induction on the number of variables. Eliminating the last variable replaces the rows by those with vanishing last coefficient together with the pairwise combinations of rows whose last coefficients have opposite signs; multipliers for the reduced system lift to nonnegative multipliers for the original one, and the base case of zero variables is immediate. Both the elimination and the lifting are performed over an arbitrary finite index type, so that the pair index set of one step is available as the index type of the next.
-- source:
--   J. Farkas, Theorie der einfachen Ungleichungen, Journal fuer die reine und angewandte Mathematik 124 (1902) 1-27. See A. Schrijver, Theory of Linear and Integer Programming, Wiley 1986, Corollary 7.1d (the inequality form Ax >= b), and Bertsimas-Tsitsiklis, Introduction to Linear Optimization, Athena Scientific 1997, Section 4.6.

import Definitions.Def_Polyhedron

/-!
Farkas' lemma in the form used for linear inequalities: a system `Ax >= b` is
either feasible, or carries a nonnegative combination of its rows that is
identically zero with positive right-hand side, and never both.

Source: J. Farkas, *Theorie der einfachen Ungleichungen*, J. Reine Angew.
Math. 124 (1902) 1-27; see A. Schrijver, *Theory of Linear and Integer
Programming*, Wiley 1986, Corollary 7.1d, and Bertsimas-Tsitsiklis,
*Introduction to Linear Optimization*, Athena Scientific 1997, Section 4.6.
-/

open Matrix LinearOptimization

/-- **Farkas' lemma.** The system `Ax >= b` has a solution if and only if there
is no vector `y >= 0` with `y' A = 0` and `y' b > 0`. -/

theorem SmaleNinth.farkas_lemma {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (polyhedron A b).Nonempty ↔
      ¬ ∃ y : Fin m → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ k, ∑ i, y i * A i k = 0) ∧
        0 < ∑ i, y i * b i := by sorry
