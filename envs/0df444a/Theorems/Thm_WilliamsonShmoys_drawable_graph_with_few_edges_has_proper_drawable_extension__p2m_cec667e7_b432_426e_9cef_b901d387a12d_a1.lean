-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_with_few_edges_has_proper_drawable_extension__p2m_cec667e7_b432_426e_9cef_b901d387a12d_a1
-- name    : WilliamsonShmoys.drawable_graph_with_few_edges_has_proper_drawable_extension__p2m_cec667e7_b432_426e_9cef_b901d387a12d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:29:07.626859+00:00
-- url     : https://prove2.me/theorems/9940682f-4c7e-48c3-97b4-7cba95f9fa9e
-- title:
--   A drawable graph below the planar edge bound admits an edge extension
-- statement:
--   For a drawable graph on at least three vertices, if its edge count is strictly below 3|V|−6, some missing edge can be added while preserving a planar drawing on the same vertex set. This removes the maximality contradiction and edge-count arithmetic from the parent; its independent proof route is to augment the drawing toward a triangulation and use Euler’s formula and face counts. The topological augmentation argument remains the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_graph_with_few_edges_has_proper_drawable_extension__p2m_cec667e7_b432_426e_9cef_b901d387a12d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hE : K.edgeFinset.card < 3 * Fintype.card V - 6) :
    ∃ (L : SimpleGraph V) (hLdec : DecidableRel L.Adj),
      (∀ {u v}, K.Adj u v → L.Adj u v) ∧
      (∃ u v, L.Adj u v ∧ ¬ K.Adj u v) ∧
      HasPlanarDrawingOn L := by sorry
