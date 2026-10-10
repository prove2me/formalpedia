-- Prove2me | Theorems.Thm_RandomListsMatching_GeneralRates_claim3_h_convex_antitone
-- name    : RandomListsMatching.GeneralRates.claim3_h_convex_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:08:24.06485+00:00
-- url     : https://prove2.me/theorems/b7bbe1fa-f0aa-467e-8b21-a809a75e85b0
-- title:
--   Claim 3 (first clause), p. 15 — for y ∈ [0, 1], h(y, x) is convex and decreasing in x ∈ [0, y]
-- statement:
--   Let $h$ be the function of Claim 2,
--   $$
--   h(y,x)=\begin{cases}\dfrac{y}{y-x}\,\bigl(e^{-x}-e^{-y}\bigr), & x\neq y,\\[4pt] y\,e^{-y}, & x=y,\end{cases}\qquad g(y,x)=h(y,0)-h(y,x).
--   $$
--   For every $y \in [0, 1]$, the function $x \mapsto h(y, x)$ is convex and (non-strictly) decreasing on the interval $[0, y]$.
--
--   This is the first clause of Claim 3 of Jaillet and Lu. Convexity of $h$ in its second argument gives the tangent bound (5), and monotonicity gives $g \ge 0$.
--
--   **Formalization Note** "Decreasing" is read as non-increasing (`AntitoneOn`), as everywhere in the mission. Both properties are stated on the closed interval $[0, y]$ only.
-- source:
--   Jaillet & Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (rev. June 2013), p. 15, Claim 3, first clause

import Mathlib
import Definitions.Def_RandomListsMatching_GeneralRates_Setting

namespace RandomListsMatching.GeneralRates

theorem claim3_h_convex_antitone (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ConvexOn ℝ (Set.Icc 0 y) (h y) ∧ AntitoneOn (h y) (Set.Icc 0 y) := by sorry

end RandomListsMatching.GeneralRates
