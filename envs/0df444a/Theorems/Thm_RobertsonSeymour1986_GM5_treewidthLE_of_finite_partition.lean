-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_treewidthLE_of_finite_partition
-- name    : RobertsonSeymour1986.GM5.treewidthLE_of_finite_partition
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T21:07:05.689992+00:00
-- url     : https://prove2.me/theorems/2e4d99aa-a752-4f98-b815-786cd462cc43
-- title:
--   Treewidth bound for a finite disjoint partition
-- statement:
--   If a finite family of pairwise disjoint vertex sets covers the graph, every edge lies within one set, and every induced subgraph on a set has treewidth at most w, then the whole graph has treewidth at most w. The empty family is allowed when the vertex type is empty. The proof route is to choose a decomposition tree for each part, connect the trees into one tree, and retain the existing bags. The remaining core is verifying the joined tree and the running-intersection condition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false

theorem RobertsonSeymour1986.GM5.treewidthLE_of_finite_partition {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (w : ℕ) (ι : Type) [Fintype ι] (C : ι → Finset V) (hcover : ∀ v : V, ∃ i, v ∈ C i) (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j)) (hedge : ∀ x y : V, G.Adj x y → ∃ i, x ∈ C i ∧ y ∈ C i) (hwidth : ∀ i, RobertsonSeymour1986.GM5.TreewidthLE (G.induce {u : V | u ∈ C i}) w) : RobertsonSeymour1986.GM5.TreewidthLE G w := by sorry
