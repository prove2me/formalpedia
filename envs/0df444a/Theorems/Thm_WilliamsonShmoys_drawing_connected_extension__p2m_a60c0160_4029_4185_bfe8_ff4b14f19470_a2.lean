-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawing_connected_extension__p2m_a60c0160_4029_4185_bfe8_ff4b14f19470_a2
-- name    : WilliamsonShmoys.drawing_connected_extension__p2m_a60c0160_4029_4185_bfe8_ff4b14f19470_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:56:40.047855+00:00
-- url     : https://prove2.me/theorems/9739b138-86b0-425b-93f7-7e4f93a209fa
-- title:
--   Connected planar extension preserves the vertex set
-- statement:
--   A graph with the given crossing-free drawing has a connected planar supergraph on the same finite vertex set. The original edge count is no larger than the extended graph’s edge count, for every decidable adjacency relation on the extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawing_connected_extension__p2m_a60c0160_4029_4185_bfe8_ff4b14f19470_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    (letI : DecidableRel L.Adj := dL
     ∃ H : SimpleGraph V,
       (∀ u v, L.Adj u v → H.Adj u v) ∧
       (∀ (dH : DecidableRel H.Adj),
         (letI : DecidableRel H.Adj := dH
          L.edgeFinset.card ≤ H.edgeFinset.card)) ∧
       H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H) := by
  sorry
