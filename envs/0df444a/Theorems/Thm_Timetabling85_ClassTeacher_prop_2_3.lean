-- Prove2me | Theorems.Thm_Timetabling85_ClassTeacher_prop_2_3
-- name    : Timetabling85.ClassTeacher.prop_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:27.591028+00:00
-- url     : https://prove2.me/theorems/626630ac-e22b-4bfd-9c56-c114fb32a24e
-- title:
--   Proposition 2.3, p. 153 — there exists a solution to CT3 for any number p ≥ 1 of days
-- statement:
--   Let $R=(r_{ij})$ be an $m\times n$ requirement matrix of nonnegative integers, with class totals $r_{i\cdot}=\sum_j r_{ij}$ and teacher totals $r_{\cdot j}=\sum_i r_{ij}$, and let $p\ge1$ be a number of days. Then there are nonnegative integers $x_{ijk}$ ($1\le i\le m$, $1\le j\le n$, $1\le k\le p$) with $\sum_{k=1}^p x_{ijk}=r_{ij}$ for all $i,j$ such that, for every day $k$ and all $i,j$,
--   $$\Big\lfloor \tfrac{r_{i\cdot}}{p}\Big\rfloor\le\sum_{j=1}^n x_{ijk}\le\Big\lceil \tfrac{r_{i\cdot}}{p}\Big\rceil,\qquad \Big\lfloor \tfrac{r_{\cdot j}}{p}\Big\rfloor\le\sum_{i=1}^m x_{ijk}\le\Big\lceil \tfrac{r_{\cdot j}}{p}\Big\rceil,\qquad \Big\lfloor \tfrac{r_{ij}}{p}\Big\rfloor\le x_{ijk}\le\Big\lceil \tfrac{r_{ij}}{p}\Big\rceil.$$
--
--   In words: the lectures can always be spread over the $p$ days so that the daily load of every class and every teacher is perfectly balanced, and at the same time the lectures of each class–teacher pair are spread as evenly as possible. Equivalently, every bipartite multigraph has a $p$-edge-colouring in which every node sees $\lfloor d/p\rfloor$ or $\lceil d/p\rceil$ edges of each colour ($d$ its degree) and every bundle of $r$ parallel edges contains $\lfloor r/p\rfloor$ or $\lceil r/p\rceil$ edges of each colour. It extends Propositions 2.1 and 2.2.
--
--   **Formalization Note** The paper says "for any $p$"; the hypothesis $p\ge1$ makes this a number of days (for $p=0$ and $R\neq0$ constraint (1) cannot hold). Floors and ceilings in the first two families are of the totals divided by $p$, not sums of entrywise floors and ceilings.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), p. 153, Proposition 2.3

import Mathlib
import Definitions.Def_Timetabling85_ClassTeacher_Problems

namespace Timetabling85.ClassTeacher

/-- Proposition 2.3 (de Werra 1985, p. 153): for every `m × n` requirement matrix `R` and every
number `p ≥ 1` of days, problem CT3 ((1) and (8)–(10)) has a solution. -/
theorem prop_2_3 {m n : ℕ} (R : Fin m → Fin n → ℕ) (p : ℕ) (hp : 0 < p) :
    ∃ x : Fin m → Fin n → Fin p → ℕ, IsCT3 R p x := by sorry

end Timetabling85.ClassTeacher
