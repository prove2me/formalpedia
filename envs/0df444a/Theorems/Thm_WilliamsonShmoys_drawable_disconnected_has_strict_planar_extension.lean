-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_disconnected_has_strict_planar_extension
-- name    : WilliamsonShmoys.drawable_disconnected_has_strict_planar_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:50:20.910947+00:00
-- url     : https://prove2.me/theorems/c083afaa-27df-4242-93ee-b46dfeb7e5d2
-- title:
--   A disconnected drawable graph has a strict drawable extension
-- statement:
--   Every disconnected finite drawable graph on at least three vertices has a drawable strict supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_disconnected_has_strict_planar_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊂ L.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
