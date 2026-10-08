-- Prove2me | Theorems.Thm_Timetabling85_ClassTeacher_prop_2_1
-- name    : Timetabling85.ClassTeacher.prop_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:55.609844+00:00
-- url     : https://prove2.me/theorems/09c1625f-21f0-4827-9e41-2ef7d0975924
-- title:
--   Proposition 2.1, p. 152 — CT1 has a solution iff every row and column sum of R is at most p (König)
-- statement:
--   Let $R=(r_{ij})$ be an $m\times n$ requirement matrix of nonnegative integers and $p$ a number of periods. Problem CT1 — find $x_{ijk}\in\{0,1\}$ with $\sum_k x_{ijk}=r_{ij}$ for all $i,j$, $\sum_j x_{ijk}\le1$ for all $i,k$ and $\sum_i x_{ijk}\le1$ for all $j,k$ — has a solution if and only if
--   $$\sum_{i=1}^m r_{ij}\le p\quad(j=1,\dots,n)\qquad\text{and}\qquad\sum_{j=1}^n r_{ij}\le p\quad(i=1,\dots,m).$$
--
--   This is König's edge-colouring theorem for bipartite multigraphs: a bipartite multigraph of maximum degree $\Delta$ can be properly edge-coloured with $p$ colours iff $\Delta\le p$. In timetabling terms, there is a timetable in $p$ periods iff no teacher and no class is involved in more than $p$ lectures.
--
--   **Formalization Note** The statement holds for every $p$, including $p=0$, where both sides say $R=0$.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), p. 152, Proposition 2.1

import Mathlib
import Definitions.Def_Timetabling85_ClassTeacher_Problems

namespace Timetabling85.ClassTeacher

/-- Proposition 2.1 (König; de Werra 1985, p. 152): CT1 has a solution iff every column sum and
every row sum of `R` is at most `p`. -/
theorem prop_2_1 {m n : ℕ} (R : Fin m → Fin n → ℕ) (p : ℕ) :
    (∃ x : Fin m → Fin n → Fin p → ℕ, IsCT1 R p x) ↔
      (∀ j, colSum R j ≤ p) ∧ (∀ i, rowSum R i ≤ p) := by sorry

end Timetabling85.ClassTeacher
