-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_components_form_finite_partition
-- name    : RobertsonSeymour1986.GM5.components_form_finite_partition
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T21:07:32.616263+00:00
-- url     : https://prove2.me/theorems/ebca2ab3-fec4-4ba5-a226-f2b835478a75
-- title:
--   Connected components form a finite partition
-- statement:
--   Under the target’s component hypothesis, produce a finite indexed partition whose parts are the connected components, cover all vertices, contain both endpoints of every edge in one part, and retain the required treewidth bound on each induced part. The proof route is to index the reachable equivalence classes and use the representative vertex’s hypothesis. For an empty graph, the empty index type and empty partition satisfy the conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false

theorem RobertsonSeymour1986.GM5.components_form_finite_partition {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (w : ℕ) (hcomp : ∀ v : V, RobertsonSeymour1986.GM5.TreewidthLE (G.induce {u : V | G.Reachable u v}) w) : ∃ (ι : Type) (_ : Fintype ι) (C : ι → Finset V), (∀ v : V, ∃ i, v ∈ C i) ∧ (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧ (∀ x y : V, G.Adj x y → ∃ i, x ∈ C i ∧ y ∈ C i) ∧ (∀ i, RobertsonSeymour1986.GM5.TreewidthLE (G.induce {u : V | u ∈ C i}) w) := by sorry
