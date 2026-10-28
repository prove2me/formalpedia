-- Prove2me | Theorems.Thm_WilliamsonShmoys_augmentation_maximal_drawable_supergraph
-- name    : WilliamsonShmoys.augmentation_maximal_drawable_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:52:14.419758+00:00
-- url     : https://prove2.me/theorems/83e40aee-6842-42a8-880a-0a95bd35b5c5
-- title:
--   A maximal drawable supergraph exists
-- statement:
--   Every drawable graph on this finite vertex type has a drawable supergraph maximal under inclusion, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.augmentation_maximal_drawable_supergraph {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hdraw : HasPlanarDrawingOn G) (hV : 3 <= Fintype.card V) : ∃ H : SimpleGraph V, HasPlanarDrawingOn H ∧ G ≤ H ∧ (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) ∧ G.edgeSet.ncard <= H.edgeSet.ncard := by sorry
