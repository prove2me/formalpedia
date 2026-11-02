-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeMaximalPlanar_augmentDisconnected__p2m_b38e7e0d_55b6_4800_9dde_424996f32dbe_a2
-- name    : WilliamsonShmoys.edgeMaximalPlanar_augmentDisconnected__p2m_b38e7e0d_55b6_4800_9dde_424996f32dbe_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:50:02.360028+00:00
-- url     : https://prove2.me/theorems/003c523f-fcf6-49dc-a9c7-eee9150479f3
-- title:
--   Augmenting a disconnected planar graph
-- statement:
--   Every disconnected finite ordered graph with at least three vertices and a planar drawing has a strict planar supergraph on the same vertices. This isolates the edge-routing argument needed by the parent; the parent then applies maximality to that supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edgeMaximalPlanar_augmentDisconnected__p2m_b38e7e0d_55b6_4800_9dde_424996f32dbe_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 ≤ Fintype.card V)
    (hdisc : ¬ K.Connected) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H ≠ K ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
