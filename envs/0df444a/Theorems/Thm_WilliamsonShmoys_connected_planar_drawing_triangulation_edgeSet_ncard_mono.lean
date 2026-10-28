-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_triangulation_edgeSet_ncard_mono
-- name    : WilliamsonShmoys.connected_planar_drawing_triangulation_edgeSet_ncard_mono
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:08:29.451659+00:00
-- url     : https://prove2.me/theorems/2dae3cda-6365-4305-abad-530c96af432f
-- title:
--   Monotonicity of edge count under adjacency inclusion
-- statement:
--   Adjacency inclusion between finite simple graphs on the same vertex type implies monotonicity of edge-set cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_triangulation_edgeSet_ncard_mono
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : ∀ ⦃u v⦄, G.Adj u v → H.Adj u v) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
