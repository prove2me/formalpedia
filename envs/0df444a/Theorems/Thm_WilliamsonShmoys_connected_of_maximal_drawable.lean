-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_of_maximal_drawable
-- name    : WilliamsonShmoys.connected_of_maximal_drawable
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T01:57:44.367592+00:00
-- url     : https://prove2.me/theorems/2886b7c5-393b-4d9d-be5c-c82e25bdee04
-- title:
--   Maximal drawable graphs are connected
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertex type is connected. The cardinality bound is needed to join distinct components by a new edge. A proof can use the planar embedding to join components through complementary regions, contradicting maximality if there are multiple components. This removes the connectivity argument from the parent; the remaining obligation is to formalize that edge-addition construction for the supplied drawing definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_of_maximal_drawable
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ J : SimpleGraph V,
      K ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ K) :
    K.Connected := by sorry
