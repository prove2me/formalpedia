-- Prove2me | Theorems.Thm_PolyhedralSOC_LowerBound_covering_claim
-- name    : PolyhedralSOC.LowerBound.covering_claim
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:49:23.246008+00:00
-- url     : https://prove2.me/theorems/32a4e465-9c2f-428a-9a37-db4a11b580c8
-- title:
--   Proposition 3.1, proof — balls of radius $\sqrt{2\varepsilon(1+\varepsilon)}$ about the $y_i$ cover $\partial((1+\varepsilon)B)$
-- statement:
--   Let $\varepsilon>0$ and let $S=\{y_1,\dots,y_N\}\subseteq\mathbb R^k$ be a finite set such that
--   1. the convex hull of $S$ contains the closed unit Euclidean ball $B$, and
--   2. every $y_i$ satisfies $\|y_i\|_2\le 1+\varepsilon$.
--
--   Then the closed Euclidean balls $B_i$ of radius $\sqrt{2\varepsilon(1+\varepsilon)}$ centred at the $y_i$ cover the sphere $\partial((1+\varepsilon)B)$: for every $y$ with $\|y\|_2=1+\varepsilon$ there is an $i$ with
--   $$\|y-y_i\|_2\le\sqrt{2\varepsilon(1+\varepsilon)}.$$
--
--   Applied to the vertices $y_i$ of the slice $G$ (which satisfies $B\subseteq G\subseteq(1+\varepsilon)B$), this is the geometric heart of the lower bound: a polytope sandwiched between two nearby balls must have vertices close to every point of the outer sphere.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 202, Proposition 3.1, proof ("We claim that the N Euclidean balls B_i centered at y_i of the radius √(2ε(1+ε)) cover the boundary of (1+ε)B")

import Mathlib
import Definitions.Def_PolyhedralSOC_Shared_LorentzCone

namespace PolyhedralSOC.LowerBound

/-- Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), Proposition 3.1, proof, p. 202 (PDF p. 10):
"We claim that the N Euclidean balls B_i centered at y_i of the radius √(2ε(1+ε)) cover the
boundary of (1+ε)B." Stated for the points `y_i` as a finite set `S ⊆ ℝ^k` whose convex hull
contains the unit Euclidean ball `B` and which lies in `(1 + ε)B` (the two properties of `G`
the proof uses): every `y` with `‖y‖₂ = 1 + ε` lies in the closed Euclidean ball of radius
`√(2ε(1+ε))` about some point of `S`. -/
theorem covering_claim {k : ℕ} {ε : ℝ} (hε : 0 < ε) (S : Finset (Fin k → ℝ))
    (hB : {y : Fin k → ℝ | Shared.eucNorm y ≤ 1} ⊆ convexHull ℝ (S : Set (Fin k → ℝ)))
    (hS : ∀ s ∈ S, Shared.eucNorm s ≤ 1 + ε) :
    ∀ y : Fin k → ℝ, Shared.eucNorm y = 1 + ε →
      ∃ s ∈ S, Shared.eucNorm (y - s) ≤ Real.sqrt (2 * ε * (1 + ε)) := by sorry

end PolyhedralSOC.LowerBound
