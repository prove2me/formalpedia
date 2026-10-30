-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_nonempty_planar_graph_has_drawable_extension__p2m_a76ab648_9831_4644_9b76_244e5b3cfa82_a2
-- name    : WilliamsonShmoys.disconnected_nonempty_planar_graph_has_drawable_extension__p2m_a76ab648_9831_4644_9b76_244e5b3cfa82_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:39:34.703342+00:00
-- url     : https://prove2.me/theorems/c52cbf91-72a0-4b4e-a159-6922131727aa
-- title:
--   A disconnected nonempty drawable graph has a strict drawable extension
-- statement:
--   Every nonempty finite disconnected graph with a drawing satisfying `HasPlanarDrawingOn` has a drawable supergraph on the same vertices with strictly more edges. The nonempty hypothesis is required: on `Empty`, the drawing predicate is vacuous and there is no strict supergraph. The lemma removes the plane-topology argument from the parent; a proof route is to find a face incident with two components and join vertices from them by a Jordan arc in that face. The remaining core obligation is proving those face-incidence and arc-construction facts for the exact continuous-arc predicate. The one-vertex case is excluded by disconnectedness; the two-isolated-vertex case is consistent with the claim because a joining arc can be drawn.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_nonempty_planar_graph_has_drawable_extension__p2m_a76ab648_9831_4644_9b76_244e5b3cfa82_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 1 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hdis : ¬ K.Connected) :
    ∃ M : SimpleGraph V,
      K.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ¬ M.edgeSet ⊆ K.edgeSet := by sorry
