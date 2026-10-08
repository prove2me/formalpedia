-- Prove2me | Theorems.Thm_Timetabling85_ClassTeacher_remaining_bounds
-- name    : Timetabling85.ClassTeacher.remaining_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:09.356572+00:00
-- url     : https://prove2.me/theorems/df30f219-cad1-4536-a11c-77cbf536a9f1
-- title:
--   §2.1, p. 153, flow sketch after Proposition 2.3 — after one balanced day, the remaining days stay balanced
-- statement:
--   Let $p\ge2$ and let $s,y$ be nonnegative integers with $\lfloor s/p\rfloor\le y\le\lceil s/p\rceil$. Then
--   $$\Big\lfloor \tfrac{s}{p}\Big\rfloor\le\Big\lfloor \tfrac{s-y}{p-1}\Big\rfloor\qquad\text{and}\qquad\Big\lceil \tfrac{s-y}{p-1}\Big\rceil\le\Big\lceil \tfrac{s}{p}\Big\rceil.$$
--
--   Applied to every entry $r_{ij}$, every row total and every column total of a requirement matrix, it says that once one day has been scheduled within the bounds of (8)–(10), the remaining lectures form a CT3 instance on $p-1$ days whose bounds lie inside the original ones. So a CT3 solution for the rest is a CT3 solution for the whole, which is what makes the day-by-day construction of the paper's sketch possible: "it will be possible to schedule the remaining lectures … without violating the right inequalities in (8)–(10)".
--
--   **Formalization Note** $s-y$ is natural-number subtraction; under the hypotheses $y\le\lceil s/p\rceil\le s$ whenever $s\ge1$ (and $y=0$ when $s=0$), so no truncation occurs.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), p. 153, §2.1, network-flow sketch after Proposition 2.3 (lower bounds l^k guaranteeing the remaining days)

import Mathlib
import Definitions.Def_Timetabling85_ClassTeacher_Problems

namespace Timetabling85.ClassTeacher

/-- The remaining days stay balanced (de Werra 1985, §2.1, p. 153): if `p ≥ 2` and a day receives
`y` of `s` lectures with `⌊s/p⌋ ≤ y ≤ ⌈s/p⌉`, the remaining `s − y` lectures over `p − 1` days
have bounds `⌊(s−y)/(p−1)⌋ ≥ ⌊s/p⌋` and `⌈(s−y)/(p−1)⌉ ≤ ⌈s/p⌉`. -/
theorem remaining_bounds (s y p : ℕ) (hp : 2 ≤ p) (hlo : lo s p ≤ y) (hhi : y ≤ hi s p) :
    lo s p ≤ lo (s - y) (p - 1) ∧ hi (s - y) (p - 1) ≤ hi s p := by sorry

end Timetabling85.ClassTeacher
