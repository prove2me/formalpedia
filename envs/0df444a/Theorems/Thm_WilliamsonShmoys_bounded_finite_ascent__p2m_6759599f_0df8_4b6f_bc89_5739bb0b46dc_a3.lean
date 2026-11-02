-- Prove2me | Theorems.Thm_WilliamsonShmoys_bounded_finite_ascent__p2m_6759599f_0df8_4b6f_bc89_5739bb0b46dc_a3
-- name    : WilliamsonShmoys.bounded_finite_ascent__p2m_6759599f_0df8_4b6f_bc89_5739bb0b46dc_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:37:53.606824+00:00
-- url     : https://prove2.me/theorems/027737b2-7675-4555-ae8d-63102bf7d1a8
-- title:
--   Bounded finite ascent reaches a terminal state
-- statement:
--   For a valid starting state whose natural-number rank is within a fixed bound, if each valid nonterminal state has a valid successor of strictly larger rank still within the bound, then some valid state is terminal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.bounded_finite_ascent__p2m_6759599f_0df8_4b6f_bc89_5739bb0b46dc_a3
    {α : Type} (P Done : α → Prop) (rank : α → ℕ) (bound : ℕ) (x0 : α)
    (hstart : P x0) (hbound : rank x0 ≤ bound)
    (hstep : ∀ x, P x → ¬ Done x →
      ∃ y, P y ∧ rank x < rank y ∧ rank y ≤ bound) :
    ∃ x, P x ∧ Done x := by sorry
