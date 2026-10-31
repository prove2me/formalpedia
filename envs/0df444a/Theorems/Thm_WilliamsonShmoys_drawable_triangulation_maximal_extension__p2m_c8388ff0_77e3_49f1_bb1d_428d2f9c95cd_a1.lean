-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_triangulation_maximal_extension__p2m_c8388ff0_77e3_49f1_bb1d_428d2f9c95cd_a1
-- name    : WilliamsonShmoys.drawable_triangulation_maximal_extension__p2m_c8388ff0_77e3_49f1_bb1d_428d2f9c95cd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:38:04.402762+00:00
-- url     : https://prove2.me/theorems/e84bb3a3-b704-43d8-b0e5-e2572be26337
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type has an inclusion-maximal drawable supergraph on the same vertex set. This removes the finite maximization step from the parent. A direct proof route is to maximize edge count among the finitely many supergraphs of K that have a planar drawing; K itself ensures this set is nonempty. The conclusion is meaningful independently of the target’s edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_triangulation_maximal_extension__p2m_c8388ff0_77e3_49f1_bb1d_428d2f9c95cd_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧ ∀ G : SimpleGraph V, H ≤ G → HasPlanarDrawingOn G → G = H := by sorry
