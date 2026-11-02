-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_bounds_sum_le__p2m_666f06c4_d624_4127_b254_b308e951621e_a1
-- name    : WilliamsonShmoys.component_bounds_sum_le__p2m_666f06c4_d624_4127_b254_b308e951621e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:10:13.937475+00:00
-- url     : https://prove2.me/theorems/640bc486-d2d6-45ba-9246-25c1bd62a2e9
-- title:
--   Sum component vertex bounds in a disconnected graph
-- statement:
--   In a finite disconnected graph, summing three times each component's vertex count minus three is at most three times the total vertex count minus six. This follows from the component supports partitioning the vertices and there being at least two components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.component_bounds_sum_le__p2m_666f06c4_d624_4127_b254_b308e951621e_a1
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V) (hdisconn : ¬ K.Connected) :
    letI : Fintype K.ConnectedComponent := Fintype.ofFinite _
    ∑ c : K.ConnectedComponent,
      (letI : Fintype {v : V // v ∈ c.supp} := Fintype.ofFinite _
       3 * Fintype.card {v : V // v ∈ c.supp} - 3) ≤ 3 * Fintype.card V - 6 := by sorry
