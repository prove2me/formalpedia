-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_graph_has_unreachable_pair__p2m_a01887ab_b605_44b6_af24_b6696d8b1f6b_a1
-- name    : WilliamsonShmoys.disconnected_graph_has_unreachable_pair__p2m_a01887ab_b605_44b6_af24_b6696d8b1f6b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:29:33.961535+00:00
-- url     : https://prove2.me/theorems/a4d49011-2c2d-4bf0-b38d-45baef7564ce
-- title:
--   A disconnected finite graph has vertices in distinct components
-- statement:
--   For a finite graph with at least three vertices, failure of connectedness yields two distinct, nonadjacent vertices that are not connected by a path.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_graph_has_unreachable_pair__p2m_a01887ab_b605_44b6_af24_b6696d8b1f6b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdis : ¬ K.Connected) :
    ∃ a b : V, a ≠ b ∧ ¬ K.Adj a b ∧ ¬ K.Reachable a b := by sorry
