-- Prove2me | Theorems.Thm_SmaleNinth_lp_fourier_motzkin_decides
-- name    : SmaleNinth.lp_fourier_motzkin_decides
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T02:42:39.882302+00:00
-- url     : https://prove2.me/theorems/6e915207-3af5-464f-bf91-7d882f60d3a9
-- title:
--   Fourier-Motzkin elimination decides feasibility
-- statement:
--   The polyhedron $\{x \in \mathbb{R}^n : Ax \ge b\}$ is nonempty if and only if the Fourier–Motzkin procedure of `Definitions.Def_SmaleNinth_FourierMotzkin`, run on the system, ends with a constant system all of whose right-hand sides are at most $0$.
--
--   This is the correctness of the elimination method in full generality: each step removes one variable, keeping the rows whose coefficient of that variable vanishes and adding, for every ordered pair of rows whose coefficients have opposite signs, the combination in which the variable cancels; after $n$ steps no variables remain and the answer is read off. The proof is an induction on the number of variables, the inductive step being that a single elimination preserves feasibility and the base case being that a system with no variables is feasible exactly when every right-hand side is nonpositive.
--
--   Two consequences are worth recording. First, feasibility of a linear system over the reals is decidable by a finite, purely algebraic procedure that uses only the ordered-field operations, so the same statement and proof hold verbatim over any ordered field. Second, the procedure is of polynomial size for each fixed number of variables: a step takes a count of $N$ rows to at most $N + N^2$, so after $n$ steps there are at most $(m+1)^{2^n}$ rows, and feasibility of an $n$-variable system is equivalent to a conjunction of that many sign conditions on explicit polynomial expressions in the entries of $A$ and $b$.
--
--   The second point is exactly where the method stops being useful for Smale's ninth problem. The bound is polynomial in the number of constraints only when the number of variables is fixed, and it is doubly exponential in the number of variables, whereas the problem asks for a number of arithmetic operations polynomial in both.
-- source:
--   J. B. J. Fourier (1826); T. Motzkin, Beitraege zur Theorie der linearen Ungleichungen, Dissertation, Basel 1936. See A. Schrijver, Theory of Linear and Integer Programming, Wiley 1986, Section 12.2 (Theorem 12.3: elimination of a variable and its iteration), and Bertsimas-Tsitsiklis, Introduction to Linear Optimization, Athena Scientific 1997, Section 2.8.

import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_FourierMotzkin

/-!
Correctness of the Fourier-Motzkin decision procedure of
`Definitions.Def_SmaleNinth_FourierMotzkin`: after eliminating all the
variables, the system is feasible exactly when every remaining constant row is
satisfiable.

Source: J. B. J. Fourier (1826) and T. Motzkin (1936); see A. Schrijver,
*Theory of Linear and Integer Programming*, Wiley 1986, Section 12.2
(Theorem 12.3), and Bertsimas-Tsitsiklis, *Introduction to Linear
Optimization*, Athena Scientific 1997, Section 2.8.
-/

open Matrix LinearOptimization

/-- **Fourier-Motzkin elimination decides feasibility in every dimension.** -/

theorem SmaleNinth.lp_fourier_motzkin_decides {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    (polyhedron A b).Nonempty ↔ ElimFeas n (fun i k => A i k) b := by sorry
