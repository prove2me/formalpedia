-- Prove2me | Theorems.Thm_SmaleNinth_exists_square_subsystem
-- name    : SmaleNinth.exists_square_subsystem
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-06T21:00:27.017641+00:00
-- url     : https://prove2.me/theorems/a9d5f352-1baf-4682-997e-1553c8334e35
-- title:
--   Basic solution carried by a nonsingular square subsystem
-- statement:
--   **Every consistent linear system has a basic solution carried by a nonsingular square subsystem.**
--
--   Let $A\in\mathbb{R}^{m\times n}$, $b\in\mathbb{R}^m$, let $I$ be a set of row indices, and suppose the subsystem $A_i x = b_i\ (i\in I)$ has a solution. Then there are an integer $r\le n$, a solution $y$ of the same subsystem, and selections of $r$ rows and $r$ columns such that
--
--   1. the $r\times r$ submatrix $A[\text{rows},\text{cols}]$ is nonsingular;
--   2. the restricted vector $(y_{c_1},\dots,y_{c_r})$ solves that square system against the corresponding entries of $b$;
--   3. $y$ vanishes at every coordinate outside the chosen columns.
--
--   **What it is for.** This is the structural half of every size estimate in linear programming. A general consistent system says nothing about how large its solutions must be, but a *square nonsingular* system is governed by Cramer's rule, and over integer data that immediately bounds the solution. This lemma is what reduces the former to the latter; the arithmetic is then `SmaleNinth.cramer_solution_bound`.
--
--   **The argument.** Among all solutions of the subsystem, choose one, $y$, whose set of zero coordinates is as large as possible; this is possible because that set is a subset of a finite index set. Let $T$ be the support of $y$.
--
--   The columns of $A_I$ indexed by $T$ are then linearly independent. Otherwise some nonzero $v$ supported in $T$ satisfies $A_I v = 0$; then $y + tv$ solves the subsystem for every $t$, and choosing $t$ to cancel one of the nonzero coordinates of $y$ produces a solution with a strictly larger zero set, contradicting the choice of $y$. (When $T$ is empty the statement holds with $r=0$.)
--
--   Write $r=|T|\le n$. Since the $r$ selected columns are independent, the matrix $A_I[\,\cdot\,,T]$ has rank $r$; as row rank equals column rank, its rows span $\mathbb{R}^{r}$, so $r$ of them form a basis. Selecting those rows gives an $r\times r$ submatrix whose rows are linearly independent, hence invertible, hence of nonzero determinant. Restricting the identity $A_I y = b_I$ to those rows, and using that $y$ vanishes off $T$, gives exactly the square system in (2).
-- source:
--   D. Bertsimas, J. N. Tsitsiklis, Introduction to Linear Optimization, Athena Scientific 1997, Section 2.2 (basic solutions) and Section 8.4 (size of solutions); B. Korte, J. Vygen, Combinatorial Optimization, 6th ed., Springer 2018, Section 4.1, proof of Theorem 4.4.

import Mathlib
import Definitions.Def_Polyhedron

open Matrix LinearOptimization

theorem SmaleNinth.exists_square_subsystem {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (I : Finset (Fin m))
    (x : Fin n → ℝ) (hx : ∀ i ∈ I, A.mulVec x i = b i) :
    ∃ (r : ℕ) (y : Fin n → ℝ) (row : Fin r → Fin m) (col : Fin r → Fin n),
      (∀ i ∈ I, A.mulVec y i = b i) ∧
      r ≤ n ∧
      (A.submatrix row col).det ≠ 0 ∧
      (A.submatrix row col).mulVec (fun k => y (col k)) = (fun k => b (row k)) ∧
      (∀ j, j ∉ Set.range col → y j = 0) := by sorry
