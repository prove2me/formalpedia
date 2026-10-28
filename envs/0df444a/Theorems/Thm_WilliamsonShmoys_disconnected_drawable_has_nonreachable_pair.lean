-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_drawable_has_nonreachable_pair
-- name    : WilliamsonShmoys.disconnected_drawable_has_nonreachable_pair
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:36:32.534468+00:00
-- url     : https://prove2.me/theorems/9d86c3ba-fb16-483c-ba26-dd5cbb36c645
-- title:
--   A disconnected graph has vertices in distinct components
-- statement:
--   A disconnected graph on a nonempty finite vertex type has two vertices that are not connected by a path. The cardinality bound supplies nonemptiness; the pair provides endpoints for the bridge augmentation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_drawable_has_nonreachable_pair
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V) (hdisc : ¬ H.Connected) :
    ∃ u v : V, ¬ H.Reachable u v := by sorry
