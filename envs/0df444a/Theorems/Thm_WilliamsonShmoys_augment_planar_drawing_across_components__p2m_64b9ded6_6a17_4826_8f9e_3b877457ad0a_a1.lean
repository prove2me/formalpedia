-- Prove2me | Theorems.Thm_WilliamsonShmoys_augment_planar_drawing_across_components__p2m_64b9ded6_6a17_4826_8f9e_3b877457ad0a_a1
-- name    : WilliamsonShmoys.augment_planar_drawing_across_components__p2m_64b9ded6_6a17_4826_8f9e_3b877457ad0a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:00:43.200978+00:00
-- url     : https://prove2.me/theorems/fda45bc4-fe61-4043-809d-f4e21b1b9ccb
-- title:
--   Join two components of a planar drawing
-- statement:
--   Given a crossing-free drawing and vertices in distinct graph components, one can add an edge between those vertices and extend the drawing to the resulting strict supergraph. The strictness follows because unreachable vertices cannot already be adjacent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.augment_planar_drawing_across_components__p2m_64b9ded6_6a17_4826_8f9e_3b877457ad0a_a1 {V : Type} [Fintype V] [LinearOrder V] (Y : SimpleGraph V) (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) (u v : V) (huv : u ≠ v) (hreach : ¬ Y.Reachable u v) : ∃ Z : SimpleGraph V, Y.edgeSet ⊂ Z.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn Z := by sorry
