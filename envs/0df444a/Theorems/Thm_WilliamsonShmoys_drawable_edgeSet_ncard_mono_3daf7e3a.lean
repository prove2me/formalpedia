-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_edgeSet_ncard_mono_3daf7e3a
-- name    : WilliamsonShmoys.drawable_edgeSet_ncard_mono_3daf7e3a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:31:27.503785+00:00
-- url     : https://prove2.me/theorems/625c767c-1bd5-4834-9519-e2c94827fbcf
-- title:
--   Monotonicity of drawable graph edge counts
-- statement:
--   For finite simple graphs on the same vertex type, graph inclusion implies that the smaller graph’s edge set has no greater cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_edgeSet_ncard_mono_3daf7e3a
    {V : Type} [Fintype V] [LinearOrder V]
    (P Q : SimpleGraph V) (hPQ : P ≤ Q) :
    P.edgeSet.ncard ≤ Q.edgeSet.ncard := by sorry
