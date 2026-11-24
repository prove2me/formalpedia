-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_Supplement_theorem_b_3
-- name    : SampleCRS.AlmostGreedy.Supplement.theorem_b_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T20:43:52.737314+00:00
-- url     : https://prove2.me/theorems/79494857-9bcb-4c97-accf-72995ef66432
-- title:
--   Theorem B.3 — discrete convex order iff equal means and stop-loss dominance
-- statement:
--   For arbitrary natural-number-supported finite-mean laws of $X,Y$, let $\delta=E[X]-E[Y]$ and $D_j=E[(X-j-1)^+]-E[(Y-j-1)^+]$. The following equivalence holds:
--   $$X\ge_{cx}Y\quad\Longleftrightarrow\quad\delta=0\ \text{and}\ D_j\ge0\text{ for every }j\in\mathbb N.$$
--   The left side tests every discrete convex real function whose expectations under both laws are finite, exactly as Definition B.3. Equality of means is part of the conclusion of the equivalence. This characterizes the discrete convex order without assuming independence or a shared underlying space.
--
--   Differences from the source:
--   - encoding: arbitrary N-supported random variables with finite means → their probability laws NatLaw on N; reason: pushforward laws preserve every tested expectation and require no common realization
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Theorem B.3, p. 39

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_discreteOrder

namespace SampleCRS.AlmostGreedy.Supplement

/-- Theorem B.3, p.39. discrete convex order iff equal means and stop-loss dominance. -/
theorem theorem_b_3 (P Q : NatLaw) :
    ConvexDominates P Q ↔ mean P - mean Q = 0 ∧ ∀ j : ℕ, 0 ≤ stopDifference P Q j := by sorry

end SampleCRS.AlmostGreedy.Supplement
