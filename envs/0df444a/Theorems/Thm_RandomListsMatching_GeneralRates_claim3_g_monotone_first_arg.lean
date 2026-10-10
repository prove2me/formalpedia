-- Prove2me | Theorems.Thm_RandomListsMatching_GeneralRates_claim3_g_monotone_first_arg
-- name    : RandomListsMatching.GeneralRates.claim3_g_monotone_first_arg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:22.779586+00:00
-- url     : https://prove2.me/theorems/d1f5c2f9-aa52-4f29-bf02-0204bc16683d
-- title:
--   Claim 3 (third clause), p. 15 — g(y, x) is increasing in y ∈ [x, ∞)
-- statement:
--   Let $h$, $g$ be the functions of Claim 2,
--   $$
--   h(y,x)=\begin{cases}\dfrac{y}{y-x}\,\bigl(e^{-x}-e^{-y}\bigr), & x\neq y,\\[4pt] y\,e^{-y}, & x=y,\end{cases}\qquad g(y,x)=h(y,0)-h(y,x).
--   $$
--   For every $x \ge 0$, the function $y \mapsto g(y, x)$ is (non-strictly) increasing on $[x, \infty)$.
--
--   This is the third clause of Claim 3 of Jaillet and Lu. It is used twice on p. 15: to compare the dummy advertiser's term $g(f_{a_d}, m_{a_d,a}) \ge g(f_a, m_{a,a_d})$, and to bound $g(f_{a_1^*}, \beta_a) \le g(1, \beta_a)$.
--
--   **Formalization Note** Claim 3 opens with "For $y \in [0,1]$", which governs its first two clauses; the third clause quantifies $y$ over $[x, \infty)$ itself, so the statement here ranges over all $y \ge x$, for every $x \ge 0$. "Increasing" is read as non-decreasing (`MonotoneOn`); at $x = 0$ the function $y \mapsto g(y, 0)$ is identically $0$, so a strict reading would be false.
-- source:
--   Jaillet & Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (rev. June 2013), p. 15, Claim 3, third clause

import Mathlib
import Definitions.Def_RandomListsMatching_GeneralRates_Setting

namespace RandomListsMatching.GeneralRates

theorem claim3_g_monotone_first_arg (x : ℝ) (hx0 : 0 ≤ x) :
    MonotoneOn (fun y => g y x) (Set.Ici x) := by sorry

end RandomListsMatching.GeneralRates
