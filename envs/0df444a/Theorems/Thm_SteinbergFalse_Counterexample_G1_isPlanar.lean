-- Prove2me | Theorems.Thm_SteinbergFalse_Counterexample_G1_isPlanar
-- name    : SteinbergFalse.Counterexample.G1_isPlanar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:10:54.378917+00:00
-- url     : https://prove2.me/theorems/59d69265-f980-4f6a-8355-ddd00e59328f
-- title:
--   §2 and Figure 1 — the graph $G_1$ is planar
-- statement:
--   Let $G_1$ be the 15-vertex graph of Figure 1. Then $G_1$ is planar: its vertices can be placed at distinct points of $\mathbb R^2$ so that, drawing each edge as the straight segment between its endpoints,
--
--   1. no vertex lies on an edge other than at that edge's endpoints, and
--   2. two edges with four distinct endpoints do not meet.
--
--   The paper asserts this in the opening paragraph of §2 ("In each of these steps, we construct a particular planar graph …") and exhibits it through the drawing of Figure 1.
--
--   **Formalization Note** Planarity is the published straight-line planarity predicate `OPG37357.IsPlanar`. For finite simple graphs it is equivalent to planarity by Fáry's theorem, and it implies topological planarity.
-- source:
--   Cohen-Addad, Hebdige, Král', Li & Salgado, Steinberg's Conjecture is false, arXiv:1604.05108v2, p. 2, §2 opening paragraph and Figure 1

import Mathlib
import Definitions.Def_opg37357_obstacle_number
import Definitions.Def_SteinbergFalse_Counterexample_G1

namespace SteinbergFalse.Counterexample

/-- §2 and Figure 1: the graph `G₁` is planar (straight-line planarity). -/
theorem G1_isPlanar : OPG37357.IsPlanar G1 := by sorry

end SteinbergFalse.Counterexample
