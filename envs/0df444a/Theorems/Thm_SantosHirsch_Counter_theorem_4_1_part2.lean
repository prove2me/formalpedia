-- Prove2me | Theorems.Thm_SantosHirsch_Counter_theorem_4_1_part2
-- name    : SantosHirsch.Counter.theorem_4_1_part2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:54:31.728687+00:00
-- url     : https://prove2.me/theorems/7b65480d-8fa0-4d0f-9f99-2397c4eca444
-- title:
--   Theorem 4.1, part 2 (polar form) — the polar spindle has no other vertices
-- statement:
--   Let $Q^\Delta\subset\mathbb R^5$ be the polar of Santos's prismatoid and $V$ the set of the 322 polar points of Table 2. Every vertex (extreme point) of $Q^\Delta$ lies in $V$:
--   $$\operatorname{ext}(Q^\Delta)\subseteq V.$$
--
--   Together with Theorem 4.1(1) this says that $V$ is exactly the vertex set of $Q^\Delta$, so the polar spindle has 322 vertices.
--
--   **Formalization Note** Polar form of "These are all the facets of $Q$": the facets of $Q$ are the vertices of its polar.
-- source:
--   Santos, A counterexample to the Hirsch conjecture, arXiv:1006.2814v3, p. 12, Theorem 4.1, part 2

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_SantosHirsch_Counter_Setting

open scoped RealInnerProductSpace

namespace SantosHirsch.Counter

/-- Theorem 4.1, part 2 (p. 12), polar form: the polar spindle has no vertices besides the
322 points of Table 2. -/
theorem theorem_4_1_part2 :
    Set.extremePoints ℝ santosSpindle ⊆ santosVertices := by sorry

end SantosHirsch.Counter
