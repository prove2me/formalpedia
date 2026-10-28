-- Prove2me | Theorems.Thm_WilliamsonShmoys_coherent_paths_spanning_tree
-- name    : WilliamsonShmoys.coherent_paths_spanning_tree
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T22:15:45.647724+00:00
-- url     : https://prove2.me/theorems/34c29ea8-d6c3-4f16-a291-ddc805a3f5e6
-- title:
--   Extract a spanning tree from coherent simple root paths
-- statement:
--   This removes path-system extraction without using planarity. For each nonroot vertex, choose its predecessor on its prescribed path. A rooted subwalk of a simple rooted path must be a prefix, since the root cannot recur. Consequently prescribed path lengths decrease by exactly one along parent edges. These edges form an acyclic connected spanning graph, and the prescribed paths lift into it with unchanged supports. The root path is trivial; singleton components therefore give the one-vertex tree. Both simplicity and coherence are retained.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

theorem WilliamsonShmoys.coherent_paths_spanning_tree
    {V : Type} [Fintype V] (G : SimpleGraph V) (root : V)
    (P : (v : {x : V // G.Reachable root x}) → G.Walk root v.val)
    (hpath : ∀ v, (P v).IsPath)
    (hprefix : ∀ u v : {x : V // G.Reachable root x},
      u.val ∈ (P v).support → (P u).IsSubwalk (P v)) :
    ∃ (R : SimpleGraph {x : V // G.Reachable root x}),
      R ≤ G.induce {x : V | G.Reachable root x} ∧ R.IsTree ∧
      ∃ (Q : (v : {x : V // G.Reachable root x}) →
          R.Walk ⟨root, SimpleGraph.Reachable.refl root⟩ v),
        (∀ v, (Q v).IsPath) ∧
        (∀ u v : {x : V // G.Reachable root x},
          u ∈ (Q v).support ↔ u.val ∈ (P v).support) := by sorry
