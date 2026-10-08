-- Prove2me | Theorems.Thm_SteinbergFalse_Counterexample_G_isPlanar
-- name    : SteinbergFalse.Counterexample.G_isPlanar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:12:50.808378+00:00
-- url     : https://prove2.me/theorems/adc191f6-00c5-447c-8aaa-0877275a3ea8
-- title:
--   §2 and Figure 3 — the graph $G$ is planar
-- statement:
--   Let $G$ be the 166-vertex graph of Figure 3. Then $G$ is planar: its vertices can be placed at distinct points of the plane $\mathbb R^2$ so that, drawing each edge as the straight segment between its endpoints,
--
--   1. no vertex lies on an edge other than at that edge's endpoints, and
--   2. two edges with four distinct endpoints do not meet.
--
--   The paper asserts the planarity of each graph of its construction in the opening paragraph of §2 and exhibits it through the drawings of Figures 1–3; it gives no separate proof.
--
--   **Formalization Note** Planarity is the published straight-line planarity predicate `OPG37357.IsPlanar`. For finite simple graphs it is equivalent to planarity by Fáry's theorem, and in any case it implies topological planarity, so asserting it is at least as strong as the paper's claim.
-- source:
--   Cohen-Addad, Hebdige, Král', Li & Salgado, Steinberg's Conjecture is false, arXiv:1604.05108v2, p. 2, §2 opening paragraph; p. 4, Figure 3

import Mathlib
import Definitions.Def_opg37357_obstacle_number
import Definitions.Def_SteinbergFalse_Counterexample_G

namespace SteinbergFalse.Counterexample

/-- §2 and Figure 3: the graph `G` is planar (straight-line planarity). -/
theorem G_isPlanar : OPG37357.IsPlanar G := by sorry

end SteinbergFalse.Counterexample
