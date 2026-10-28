-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_edge_count_aggregation_piecewise_sum_bound
-- name    : WilliamsonShmoys.component_edge_count_aggregation_piecewise_sum_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:28:43.151067+00:00
-- url     : https://prove2.me/theorems/639fce09-0b0f-4aad-ab4e-0c508cbe4c2e
-- title:
--   Aggregate the piecewise local allowances
-- statement:
--   If the part sizes sum to the total vertex count and each part's value obeys the stated size-dependent bound, then the sum of all part values is at most three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.component_edge_count_aggregation_piecewise_sum_bound
    {V : Type} [Fintype V]
    (C : Finset (Finset V))
    (f : Finset V → Nat)
    (hCardSum : C.sum Finset.card = Fintype.card V)
    (hPiece : ∀ S ∈ C,
      f S ≤ (if S.card < 3 then S.card / 2 else 3 * S.card - 6))
    (hV : 3 ≤ Fintype.card V) :
    C.sum f ≤ 3 * Fintype.card V - 6 := by sorry
