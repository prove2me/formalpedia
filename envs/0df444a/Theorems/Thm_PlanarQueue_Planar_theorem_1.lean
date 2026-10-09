-- Prove2me | Theorems.Thm_PlanarQueue_Planar_theorem_1
-- name    : PlanarQueue.Planar.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:24:39.42317+00:00
-- url     : https://prove2.me/theorems/53e3305d-0867-4738-8bed-1be2cff889f1
-- title:
--   Theorem 1 — every planar graph has a 49-queue layout
-- statement:
--   Every finite planar graph $G$ has a queue layout using at most $49$ queues:
--
--   $$
--   \operatorname{qn}(G)\le49.
--   $$
--
--   This resolves the bounded queue-number question for planar graphs with the explicit bound obtained in the paper.
--
--   **Formalization Note** The printed Theorem 1 says that queue-number is bounded; the paper states $49$ immediately after the theorem and derives it again on page 16. The bound is uniform over all finite simple planar graphs.
-- source:
--   Dujmović, Joret, Micek, Morin, Ueckerdt, Wood, Planar graphs have bounded queue-number, arXiv:1904.04791v5, p. 5, Theorem 1 and bound 49; p. 16, derivation

import Mathlib
import Definitions.Def_PlanarQueue_Planar_Setting

namespace PlanarQueue.Planar

/-- Theorem 1, using the bound 49 obtained on pages 5 and 16. -/
theorem theorem_1 (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsPlanar G) :
    HasQueueLayout G 49 := by sorry

end PlanarQueue.Planar
