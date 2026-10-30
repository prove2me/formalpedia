-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_supergraph__p2m_728b0cab_3e49_4ae4_a8bb_3f99be3d53bf_a2
-- name    : WilliamsonShmoys.disconnected_planar_supergraph__p2m_728b0cab_3e49_4ae4_a8bb_3f99be3d53bf_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:21:20.372696+00:00
-- url     : https://prove2.me/theorems/f7639c38-a73f-4cc2-ae8d-a0f2b8768f46
-- title:
--   A disconnected planar drawing has a strict planar supergraph
-- statement:
--   If a nonempty finite ordered vertex type carries a disconnected graph with a crossing-free drawing, there is a strictly larger simple supergraph on the same vertices that also has a crossing-free drawing. This child isolates the planar augmentation argument. Its proof route is to use the outer face of component embeddings to connect two components with an added arc; nonemptiness is retained to avoid empty-type boundary failures. The parent then applies maximality to this strict planar supergraph and obtains a contradiction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_planar_supergraph__p2m_728b0cab_3e49_4ae4_a8bb_3f99be3d53bf_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 0 < Fintype.card V) (hDisconnected : ¬ H.Connected) : ∃ G : SimpleGraph V, H ≤ G ∧ G ≠ H ∧ WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
