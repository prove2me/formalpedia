-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_edge_maximal_extension__p2m_f1c5cd14_5ded_4838_bd8a_1ed332d55054_a1
-- name    : WilliamsonShmoys.drawable_edge_maximal_extension__p2m_f1c5cd14_5ded_4838_bd8a_1ed332d55054_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:09:45.277058+00:00
-- url     : https://prove2.me/theorems/c1a57574-0535-44da-8b9b-b06fed78fa1f
-- title:
--   Drawable graph has an edge-maximal drawable extension
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertices that is maximal under edge inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_edge_maximal_extension__p2m_f1c5cd14_5ded_4838_bd8a_1ed332d55054_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    exists H : SimpleGraph V, exists instH : DecidableRel H.Adj,
      (letI : DecidableRel H.Adj := instH
       G.edgeFinset ⊆ H.edgeFinset /\
       HasPlanarDrawingOn H /\
       ∀ (K : SimpleGraph V) [DecidableRel K.Adj],
         H.edgeFinset ⊆ K.edgeFinset → HasPlanarDrawingOn K →
           K.edgeFinset ⊆ H.edgeFinset) := by sorry
