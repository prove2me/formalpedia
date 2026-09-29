-- Prove2me | Theorems.Thm_SmaleNinth_elim_card_bound
-- name    : SmaleNinth.elim_card_bound
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T02:47:33.707865+00:00
-- url     : https://prove2.me/theorems/51d78df9-e2af-4ae1-8c7c-5d81802b7551
-- title:
--   Size of the Fourier-Motzkin eliminated system
-- statement:
--   One step of Fourier–Motzkin elimination replaces a system of $N$ inequalities by one indexed by the rows together with the ordered pairs of rows, that is by $N + N^2$ inequalities. Iterating from $m$ inequalities, the number of rows after $n$ eliminations therefore satisfies
--
--   $$\#\,\mathrm{ElimIdx}(n, m) + 1 \ \le\ (m+1)^{2^n} .$$
--
--   The proof is an induction on $n$ using $N + N^2 + 1 \le (N+1)^2$, which is what makes the shifted quantity $\#+1$ the right one to bound: the bound squares at each step exactly as the exponent doubles.
--
--   Combined with `SmaleNinth.lp_fourier_motzkin_decides`, this makes the classical decision procedure for real linear feasibility quantitative. Feasibility of a system of $m$ inequalities in $n$ variables is equivalent to a conjunction of at most $(m+1)^{2^n}$ sign conditions, each of them an explicit polynomial expression in the entries of the system. For a fixed number of variables that is polynomial in the number of constraints, which is the general form of the fixed-dimension results and covers the two machine theorems of this mission as the cases $n = 1$ and $n = 2$.
--
--   It also marks precisely where the method fails to bear on the mission's goal. The exponent $2^n$ is doubly exponential in the number of variables, whereas Smale's ninth problem asks for a number of arithmetic operations polynomial in the number of constraints and variables together. Any strongly polynomial algorithm must therefore avoid materialising the eliminated systems.
-- source:
--   Growth of the number of inequalities under Fourier-Motzkin elimination; see A. Schrijver, Theory of Linear and Integer Programming, Wiley 1986, Section 12.2, and Bertsimas-Tsitsiklis, Introduction to Linear Optimization, Athena Scientific 1997, Section 2.8.

import Definitions.Def_SmaleNinth_ElimIdx

/-!
The size of the Fourier-Motzkin decision procedure: after eliminating `n`
variables from a system of `m` inequalities, the number of remaining rows is at
most `(m+1)^(2^n) - 1`.

Source: the growth `N ↦ N + N^2` of the number of inequalities under one
elimination step; see A. Schrijver, *Theory of Linear and Integer
Programming*, Wiley 1986, Section 12.2.
-/

/-- **Size of the eliminated system.** -/

theorem SmaleNinth.elim_card_bound (n m : ℕ) :
    Fintype.card (SmaleNinth.ElimIdx n (Fin m)) + 1 ≤ (m + 1) ^ (2 ^ n) := by sorry
