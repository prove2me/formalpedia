-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_treewidthLE_of_finite_partition_decompositions
-- name    : RobertsonSeymour1986.GM5.treewidthLE_of_finite_partition_decompositions
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T21:16:20.826177+00:00
-- url     : https://prove2.me/theorems/fce24efb-bfd8-4fe7-ac38-8166377f5d78
-- title:
--   Glue bounded decompositions of a finite disjoint partition
-- statement:
--   Given bounded tree decompositions of each induced part, glue them into a bounded tree decomposition of the whole graph, assuming the parts form a finite disjoint cover and every edge lies within a part.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false

theorem RobertsonSeymour1986.GM5.treewidthLE_of_finite_partition_decompositions {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (w : ℕ) (ι : Type) [Fintype ι] (C : ι → Finset V) (hcover : ∀ v : V, ∃ i, v ∈ C i) (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j)) (hedge : ∀ x y : V, G.Adj x y → ∃ i, x ∈ C i ∧ y ∈ C i) (hdecomps : ∀ i, ∃ (T : Type) (_ : Fintype T) (t : SimpleGraph T) (X : T → Finset {u : V // u ∈ C i}), RobertsonSeymour1986.GM5.IsTreeDecomposition (G.induce {u : V | u ∈ C i}) t X ∧ ∀ s : T, (X s).card ≤ w + 1) : RobertsonSeymour1986.GM5.TreewidthLE G w := by sorry
