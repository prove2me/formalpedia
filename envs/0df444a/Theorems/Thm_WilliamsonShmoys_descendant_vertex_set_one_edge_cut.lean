-- Prove2me | Theorems.Thm_WilliamsonShmoys_descendant_vertex_set_one_edge_cut
-- name    : WilliamsonShmoys.descendant_vertex_set_one_edge_cut
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T22:41:17.800852+00:00
-- url     : https://prove2.me/theorems/b2323ce6-2594-49ac-bbdf-aadee2c54391
-- title:
--   A rooted tree descendant set is connected with at most one boundary edge
-- statement:
--   The vertices whose unique root path contains `v` form a nonempty connected subtree. Every edge crossing from this set to its complement is the same unoriented edge, if any. For `v = root` the set is all vertices and there is no crossing edge; for a nonroot vertex the possible crossing edge is its parent edge. This removes the rooted-path and tree-boundary work from the face-connectivity argument. A proof route uses uniqueness of paths in a tree and the fact that each `Q x` is a path.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
set_option autoImplicit false

theorem WilliamsonShmoys.descendant_vertex_set_one_edge_cut
    {V : Type} [Fintype V] (R : SimpleGraph V) (hR : R.IsTree)
    (root : V) (Q : (x : V) → R.Walk root x)
    (hQ : ∀ x, (Q x).IsPath) (v : V) :
    let S : Set V := {x | v ∈ (Q x).support}
    S.Nonempty ∧ (R.induce S).Connected ∧
      ∀ a b c d : V, R.Adj a b → a ∈ S → b ∉ S →
        R.Adj c d → c ∈ S → d ∉ S →
          (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by sorry
