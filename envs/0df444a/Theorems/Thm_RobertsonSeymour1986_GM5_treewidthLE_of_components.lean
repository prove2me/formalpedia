-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_treewidthLE_of_components
-- name    : RobertsonSeymour1986.GM5.treewidthLE_of_components
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T20:58:09.814235+00:00
-- url     : https://prove2.me/theorems/32f8a3f0-3c48-4e92-944b-e0e17343811b
-- title:
--   Combining tree decompositions of connected components
-- statement:
--   If every connected component of a finite simple graph has a tree decomposition with bags of size at most w+1, then the whole graph has such a decomposition. The empty graph is included: it admits a one-node decomposition with an empty bag.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false

theorem RobertsonSeymour1986.GM5.treewidthLE_of_components {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (w : ℕ) (hcomp : ∀ v : V, RobertsonSeymour1986.GM5.TreewidthLE (G.induce {u : V | G.Reachable u v}) w) : RobertsonSeymour1986.GM5.TreewidthLE G w := by sorry
