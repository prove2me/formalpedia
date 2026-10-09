-- Prove2me | Theorems.Thm_PlanarQueue_Planar_lemma_5
-- name    : PlanarQueue.Planar.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:24:27.836641+00:00
-- url     : https://prove2.me/theorems/1576ebc4-c97d-4bb7-b9ad-6498a28cac96
-- title:
--   Lemma 5 — planar treewidth-three graphs have five queues
-- statement:
--   Every finite planar graph $G$ with treewidth at most $3$ has a queue layout using at most $5$ queues:
--
--   $$
--   \operatorname{tw}(G)\le 3
--   \quad\Longrightarrow\quad
--   \operatorname{qn}(G)\le 5.
--   $$
--
--   This is the queue bound for the quotient graph supplied by Theorem 15.
--
--   **Formalization Note** Planarity is an explicit hypothesis. Treewidth at most $3$ uses the published tree-decomposition predicate, which requires bags of size at most $4$.
-- source:
--   Dujmović, Joret, Micek, Morin, Ueckerdt, Wood, Planar graphs have bounded queue-number, arXiv:1904.04791v5, p. 7, Lemma 5, citing [2, 83]

import Mathlib
import Definitions.Def_PlanarQueue_Planar_Setting

namespace PlanarQueue.Planar

/-- Lemma 5: planar graphs of treewidth at most three have a five-queue layout. -/
theorem lemma_5 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hplanar : IsPlanar G)
    (htw : RobertsonSeymour1986.GM5.TreewidthLE G 3) :
    HasQueueLayout G 5 := by sorry

end PlanarQueue.Planar
