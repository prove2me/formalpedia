-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_graph_has_drawable_extension__p2m_a76ab648_9831_4644_9b76_244e5b3cfa82_a1
-- name    : WilliamsonShmoys.disconnected_planar_graph_has_drawable_extension__p2m_a76ab648_9831_4644_9b76_244e5b3cfa82_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T00:59:10.800627+00:00
-- url     : https://prove2.me/theorems/a393ff4b-017d-46ee-b1cc-c797bd54a679
-- title:
--   A disconnected drawable graph has a strict drawable extension
-- statement:
--   Every disconnected finite drawable graph has a drawable supergraph on the same vertices with strictly more edges. The source is the plane-topology argument described in the explanation. This removes all topological drawing work from the parent; an independent proof route is to use face incidence of the embedded components and join two components by a Jordan arc in a common face. The remaining core obligation is proving that incidence and arc construction for the exact continuous-arc definition. Its disconnectedness hypothesis excludes the zero- and one-vertex boundary cases, and the two isolated vertex case admits a direct joining arc.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_planar_graph_has_drawable_extension__p2m_a76ab648_9831_4644_9b76_244e5b3cfa82_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hdis : ¬ K.Connected) :
    ∃ M : SimpleGraph V,
      K.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ¬ M.edgeSet ⊆ K.edgeSet := by sorry
