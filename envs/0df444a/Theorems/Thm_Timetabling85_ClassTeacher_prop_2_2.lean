-- Prove2me | Theorems.Thm_Timetabling85_ClassTeacher_prop_2_2
-- name    : Timetabling85.ClassTeacher.prop_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:59.194994+00:00
-- url     : https://prove2.me/theorems/555343bd-4785-427d-938d-5348bd8e2b45
-- title:
--   Proposition 2.2, p. 152 — CT2 has a solution iff column sums are at most p·b_j and row sums at most p·a_i
-- statement:
--   Let $R=(r_{ij})$ be an $m\times n$ requirement matrix of nonnegative integers, $p$ a number of days, and $a_1,\dots,a_m$, $b_1,\dots,b_n$ positive integers (the maximum daily loads of the classes and the teachers). Problem CT2 — find nonnegative integers $x_{ijk}$ with $\sum_k x_{ijk}=r_{ij}$ for all $i,j$, $\sum_j x_{ijk}\le a_i$ for all $i,k$ and $\sum_i x_{ijk}\le b_j$ for all $j,k$ — has a solution if and only if
--   $$\sum_{i=1}^m r_{ij}\le p\,b_j\quad(j=1,\dots,n)\qquad\text{and}\qquad\sum_{j=1}^n r_{ij}\le p\,a_i\quad(i=1,\dots,m).$$
--
--   In edge-colouring terms: the edges of the bipartite multigraph can be coloured with $p$ colours so that at most $a_i$ (resp. $b_j$) edges at $c_i$ (resp. $t_j$) share a colour iff the degree of each node is at most $p$ times its bound.
--
--   **Formalization Note** Positivity of $a_i$ and $b_j$ is the paper's hypothesis ("a positive integer"). The statement is for every $p$, including $p=0$.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), p. 152, Proposition 2.2

import Mathlib
import Definitions.Def_Timetabling85_ClassTeacher_Problems

namespace Timetabling85.ClassTeacher

/-- Proposition 2.2 (de Werra 1985, p. 152): for positive integers `a i`, `b j`, CT2 has a solution
iff `∑_i r_ij ≤ p b_j` for every `j` and `∑_j r_ij ≤ p a_i` for every `i`. -/
theorem prop_2_2 {m n : ℕ} (R : Fin m → Fin n → ℕ) (p : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) :
    (∃ x : Fin m → Fin n → Fin p → ℕ, IsCT2 R p a b x) ↔
      (∀ j, colSum R j ≤ p * b j) ∧ (∀ i, rowSum R i ≤ p * a i) := by sorry

end Timetabling85.ClassTeacher
