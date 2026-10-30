-- Prove2me | Theorems.Thm_WilliamsonShmoys_completion_from_step_and_bound__p2m_25e5c99b_0e98_467d_950b_52f83507dff1_a1
-- name    : WilliamsonShmoys.completion_from_step_and_bound__p2m_25e5c99b_0e98_467d_950b_52f83507dff1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:33:38.381307+00:00
-- url     : https://prove2.me/theorems/a718948a-c155-4532-bf04-f1524b78d8bb
-- title:
--   Iterate edge extensions to an exact bound
-- statement:
--   For any graph property closed under the supplied one-edge extension step, if all graphs with the property obey the given edge bound, repeated extensions produce a supergraph attaining that bound exactly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.completion_from_step_and_bound__p2m_25e5c99b_0e98_467d_950b_52f83507dff1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hbound : ∀ G, P G → 3 <= Fintype.card V →
      G.edgeSet.ncard <= 3 * Fintype.card V - 6)
    (hstep : ∀ G, P G → 3 <= Fintype.card V →
      G.edgeSet.ncard < 3 * Fintype.card V - 6 →
      ∃ K : SimpleGraph V,
        G ≤ K ∧ P K ∧ K.edgeSet.ncard = G.edgeSet.ncard + 1)
    (H : SimpleGraph V)
    (hH : P H)
    (hV : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ P K ∧ K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
