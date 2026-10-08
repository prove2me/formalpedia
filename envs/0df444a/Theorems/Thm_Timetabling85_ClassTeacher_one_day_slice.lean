-- Prove2me | Theorems.Thm_Timetabling85_ClassTeacher_one_day_slice
-- name    : Timetabling85.ClassTeacher.one_day_slice
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:54.171283+00:00
-- url     : https://prove2.me/theorems/19ecfd6d-7ef6-43d6-93e1-72559f42aa2c
-- title:
--   §2.1, p. 153, flow sketch after Proposition 2.3 — one day of a balanced schedule exists
-- statement:
--   Let $R=(r_{ij})$ be an $m\times n$ matrix of nonnegative integers with row totals $r_{i\cdot}=\sum_j r_{ij}$ and column totals $r_{\cdot j}=\sum_i r_{ij}$, and let $p\ge1$. Then there is an $m\times n$ matrix $y=(y_{ij})$ of nonnegative integers such that for all $i,j$
--   $$\Big\lfloor \tfrac{r_{ij}}{p}\Big\rfloor\le y_{ij}\le\Big\lceil \tfrac{r_{ij}}{p}\Big\rceil,\qquad \Big\lfloor \tfrac{r_{i\cdot}}{p}\Big\rfloor\le\sum_{j=1}^n y_{ij}\le\Big\lceil \tfrac{r_{i\cdot}}{p}\Big\rceil,\qquad \Big\lfloor \tfrac{r_{\cdot j}}{p}\Big\rfloor\le\sum_{i=1}^m y_{ij}\le\Big\lceil \tfrac{r_{\cdot j}}{p}\Big\rceil.$$
--
--   The matrix $y$ is the content of one day $k$ of a CT3 schedule: it satisfies the bounds (8), (9) and (10) simultaneously. In the paper it is the compatible flow of step $k$ in the network $s\to c_i\to t_j\to t$ with lower bounds $l^k$ and capacities $c^k$; here it is stated directly about the matrix.
--
--   **Formalization Note** The hypothesis $p\ge1$ is added: for $p=0$ Lean's division gives $s/0=0$, and the paper's "any $p$" means any number of days.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), p. 153, §2.1, network-flow sketch after Proposition 2.3 (step k of the p compatible-flow problems)

import Mathlib
import Definitions.Def_Timetabling85_ClassTeacher_Problems

namespace Timetabling85.ClassTeacher

/-- One step of the flow construction (de Werra 1985, §2.1, p. 153): for `p ≥ 1` there is a
one-day slice `y` of `R` meeting the bounds of (8), (9) and (10). -/
theorem one_day_slice {m n : ℕ} (R : Fin m → Fin n → ℕ) (p : ℕ) (hp : 0 < p) :
    ∃ y : Fin m → Fin n → ℕ,
      (∀ i j, lo (R i j) p ≤ y i j ∧ y i j ≤ hi (R i j) p) ∧
      (∀ i, lo (rowSum R i) p ≤ ∑ j, y i j ∧ ∑ j, y i j ≤ hi (rowSum R i) p) ∧
      (∀ j, lo (colSum R j) p ≤ ∑ i, y i j ∧ ∑ i, y i j ≤ hi (colSum R j) p) := by sorry

end Timetabling85.ClassTeacher
