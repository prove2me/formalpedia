-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_drawable_augmentation_retry2
-- name    : WilliamsonShmoys.drawable_graph_has_maximal_drawable_augmentation_retry2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:02:05.233287+00:00
-- url     : https://prove2.me/theorems/dc921334-5149-4bc0-9086-a027a5239bb2
-- title:
--   A drawable graph has a maximal drawable augmentation
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that is maximal among drawable supergraphs on that vertex set. This removes extension existence and maximality from the parent. Independently, one can use finiteness of the set of simple graphs on the vertex type, restrict to drawable extensions of U, and choose an extension with a largest edge set. The boundary case of an empty vertex type is covered because U itself is an extension; no vertex-count lower bound is needed for this lemma.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_maximal_drawable_augmentation_retry2
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hUdraw : WilliamsonShmoys.HasPlanarDrawingOn U) :
    Exists fun W : SimpleGraph V =>
      U <= W /\ WilliamsonShmoys.HasPlanarDrawingOn W /\
      (forall X : SimpleGraph V, W <= X ->
        WilliamsonShmoys.HasPlanarDrawingOn X -> X <= W) := by sorry
