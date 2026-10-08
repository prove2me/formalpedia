-- Prove2me | Theorems.Thm_SteinbergFalse_Counterexample_G2_isPlanar
-- name    : SteinbergFalse.Counterexample.G2_isPlanar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:11:49.842108+00:00
-- url     : https://prove2.me/theorems/fd984e47-6fec-4990-9d6b-773730d70490
-- title:
--   §2 and Figure 2 — the graph $G_2$ is planar
-- statement:
--   Let $G_2$ be the 42-vertex graph of Figure 2. Then $G_2$ is planar: its vertices can be placed at distinct points of $\mathbb R^2$ so that, drawing each edge as the straight segment between its endpoints,
--
--   1. no vertex lies on an edge other than at that edge's endpoints, and
--   2. two edges with four distinct endpoints do not meet.
--
--   The paper asserts this in the opening paragraph of §2 and exhibits it through the drawing of Figure 2.
--
--   **Formalization Note** Planarity is the published straight-line planarity predicate `OPG37357.IsPlanar`. For finite simple graphs it is equivalent to planarity by Fáry's theorem, and it implies topological planarity.
-- source:
--   Cohen-Addad, Hebdige, Král', Li & Salgado, Steinberg's Conjecture is false, arXiv:1604.05108v2, p. 2, §2 opening paragraph; p. 3, Figure 2

import Mathlib
import Definitions.Def_opg37357_obstacle_number
import Definitions.Def_SteinbergFalse_Counterexample_G2

namespace SteinbergFalse.Counterexample

/-- §2 and Figure 2: the graph `G₂` is planar (straight-line planarity). -/
theorem G2_isPlanar : OPG37357.IsPlanar G2 := by sorry

end SteinbergFalse.Counterexample
