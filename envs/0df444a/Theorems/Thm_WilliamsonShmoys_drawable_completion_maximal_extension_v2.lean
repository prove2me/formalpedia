-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_completion_maximal_extension_v2
-- name    : WilliamsonShmoys.drawable_completion_maximal_extension_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:06:47.161237+00:00
-- url     : https://prove2.me/theorems/c5e1858a-2a3c-4141-baf9-9c855ce6f06f
-- title:
--   Maximal drawable extension on the same vertices
-- statement:
--   Extend the given drawable graph to a drawable graph on the same vertex type that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_completion_maximal_extension_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V) :
    exists N : SimpleGraph V,
      (forall {u v}, M.Adj u v -> N.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn N /\
      (forall P : SimpleGraph V,
        (forall {u v}, N.Adj u v -> P.Adj u v) ->
        WilliamsonShmoys.HasPlanarDrawingOn P ->
        (forall {u v}, P.Adj u v -> N.Adj u v)) := by sorry
