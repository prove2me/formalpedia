-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_completion_maximal_extension
-- name    : WilliamsonShmoys.drawable_completion_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:44:51.566173+00:00
-- url     : https://prove2.me/theorems/a0527ee5-0663-41ae-b287-2eed4e5d4a01
-- title:
--   Finite maximal drawable extension
-- statement:
--   Any drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_completion_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn N) :
    exists P : SimpleGraph V,
      (forall {u v}, N.Adj u v -> P.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn P /\
      (forall Q : SimpleGraph V,
        (forall {u v}, P.Adj u v -> Q.Adj u v) ->
        WilliamsonShmoys.HasPlanarDrawingOn Q -> Q = P) := by sorry
