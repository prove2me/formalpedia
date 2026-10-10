-- Prove2me | Theorems.Thm_RandomListsMatching_GeneralRates_claim3_g_concave_monotone
-- name    : RandomListsMatching.GeneralRates.claim3_g_concave_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:11.217227+00:00
-- url     : https://prove2.me/theorems/56be67f8-8a45-45bf-93d0-e5096021214f
-- title:
--   Claim 3 (second clause), p. 15 — for y ∈ [0, 1], g(y, x) is concave and increasing in x ∈ [0, y]
-- statement:
--   Let $h$, $g$ be the functions of Claim 2,
--   $$
--   h(y,x)=\begin{cases}\dfrac{y}{y-x}\,\bigl(e^{-x}-e^{-y}\bigr), & x\neq y,\\[4pt] y\,e^{-y}, & x=y,\end{cases}\qquad g(y,x)=h(y,0)-h(y,x).
--   $$
--   For every $y \in [0, 1]$, the function $x \mapsto g(y, x)$ is concave and (non-strictly) increasing on the interval $[0, y]$.
--
--   This is the second clause of Claim 3 of Jaillet and Lu. Together with $g(y, 0) = 0$, concavity yields the chord bound $g(f, m) \ge (m/\beta)\, g(f, \beta)$ for $0 \le m \le \beta \le f$ used on p. 15.
--
--   **Formalization Note** "Increasing" is read as non-decreasing (`MonotoneOn`). Both properties are stated on $[0, y]$ only.
-- source:
--   Jaillet & Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (rev. June 2013), p. 15, Claim 3, second clause

import Mathlib
import Definitions.Def_RandomListsMatching_GeneralRates_Setting

namespace RandomListsMatching.GeneralRates

theorem claim3_g_concave_monotone (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ConcaveOn ℝ (Set.Icc 0 y) (g y) ∧ MonotoneOn (g y) (Set.Icc 0 y) := by sorry

end RandomListsMatching.GeneralRates
