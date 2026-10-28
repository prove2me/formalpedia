-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_drawable_has_drawable_extension
-- name    : WilliamsonShmoys.disconnected_drawable_has_drawable_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:14:49.814985+00:00
-- url     : https://prove2.me/theorems/fec9e808-9f46-47aa-a192-627ce7c10f4a
-- title:
--   A disconnected drawable graph has a strict drawable extension
-- statement:
--   Any disconnected drawable graph on at least three vertices has a strict supergraph on the same vertex type that is also drawable. This is the bridge-augmentation step needed to contradict maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_drawable_has_drawable_extension
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V)
    (hdisc : ¬ H.Connected) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ K ≠ H := by sorry
