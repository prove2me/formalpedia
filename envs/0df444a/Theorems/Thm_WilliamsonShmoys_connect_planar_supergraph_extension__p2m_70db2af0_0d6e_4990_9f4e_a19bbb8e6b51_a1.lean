-- Prove2me | Theorems.Thm_WilliamsonShmoys_connect_planar_supergraph_extension__p2m_70db2af0_0d6e_4990_9f4e_a19bbb8e6b51_a1
-- name    : WilliamsonShmoys.connect_planar_supergraph_extension__p2m_70db2af0_0d6e_4990_9f4e_a19bbb8e6b51_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:17:15.031978+00:00
-- url     : https://prove2.me/theorems/0bb86acf-18ae-4f3f-97ae-6c52ab0a1177
-- title:
--   Connected planar supergraph extension
-- statement:
--   Every finite graph with the specified planar drawing has a connected planar supergraph on the same vertex type that retains all of its edges. This separates the geometric component-joining construction from the target’s edge-count argument. The formal statement preserves the target’s hypotheses and drawing predicate; the finite vertex bound also rules out the empty vertex type. A proof route is to use the faces of the finite embedding to add noncrossing edges between components until only one component remains. The topological augmentation is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.connect_planar_supergraph_extension__p2m_70db2af0_0d6e_4990_9f4e_a19bbb8e6b51_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, L.edgeSet ⊆ H.edgeSet ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
