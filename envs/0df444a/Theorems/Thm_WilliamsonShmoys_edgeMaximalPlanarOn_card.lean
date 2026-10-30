-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeMaximalPlanarOn_card
-- name    : WilliamsonShmoys.edgeMaximalPlanarOn_card
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:27:47.87199+00:00
-- url     : https://prove2.me/theorems/7b8669e3-d596-4e0d-9033-72c379cabd1a
-- title:
--   Edge-maximal planar graphs have 3n−6 edges
-- statement:
--   A finite simple graph with at least three vertices, drawn according to HasPlanarDrawingOn and admitting no strict planar edge-supergraph on the same vertex set, has exactly 3n−6 edges. The independent proof route is the classical triangulation argument: maximality forces every face boundary to be a triangle, then Euler’s formula and double-counting face-edge incidences give 3n−6. The delicate formal work is translating the arc predicate, including disconnected drawings and face boundaries, into that embedding argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edgeMaximalPlanarOn_card
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N.edgeSet ⊂ P.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn P) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
