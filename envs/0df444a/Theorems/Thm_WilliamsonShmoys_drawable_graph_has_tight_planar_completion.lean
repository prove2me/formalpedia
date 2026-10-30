-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_tight_planar_completion
-- name    : WilliamsonShmoys.drawable_graph_has_tight_planar_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:48:43.529715+00:00
-- url     : https://prove2.me/theorems/44b30fe4-6bd0-4f77-a817-96c82473dfd0
-- title:
--   Exact edge-count planar completion
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges. This removes the face-count construction from the parent: maximality identifies the completion with the original graph, after which the parent chooses f=2|V|−4. A proof route is to extend the finite drawing to an edge-maximal planar graph, represent its faces in a finite embedding, and combine Euler’s formula with the fact that maximality forces triangular faces. The topological extension and face-count argument remain the core obligation in this child. The source context is Williamson and Shmoys, Section 10.2, Theorem 10.11, pp. 270–272 ([author manuscript](https://www.designofapproxalgs.com/book.pdf)).
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_tight_planar_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 <= Fintype.card V) :
    exists K : SimpleGraph V,
      N <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
