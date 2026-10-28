-- Prove2me | Theorems.Thm_WilliamsonShmoys_augmentation_maximal_drawable_connected
-- name    : WilliamsonShmoys.augmentation_maximal_drawable_connected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T14:58:07.384377+00:00
-- url     : https://prove2.me/theorems/dc566a76-5c3d-49ce-8cbf-6d2834a5e2ef
-- title:
--   A maximal drawable graph is connected
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph on the same vertices is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.augmentation_maximal_drawable_connected {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hdraw : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V) (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) : H.Connected := by sorry
