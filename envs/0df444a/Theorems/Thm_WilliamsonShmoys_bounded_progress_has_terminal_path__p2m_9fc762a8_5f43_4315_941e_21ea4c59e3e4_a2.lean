-- Prove2me | Theorems.Thm_WilliamsonShmoys_bounded_progress_has_terminal_path__p2m_9fc762a8_5f43_4315_941e_21ea4c59e3e4_a2
-- name    : WilliamsonShmoys.bounded_progress_has_terminal_path__p2m_9fc762a8_5f43_4315_941e_21ea4c59e3e4_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:28:38.473568+00:00
-- url     : https://prove2.me/theorems/cbe37b09-4d1a-47e1-867f-6fdffa7c0ff4
-- title:
--   Bounded strict progress reaches a terminal state
-- statement:
--   If a natural-valued rank is globally bounded and every nonterminal state has a strictly higher-ranked successor, every state has a finite path to a terminal state.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.bounded_progress_has_terminal_path__p2m_9fc762a8_5f43_4315_941e_21ea4c59e3e4_a2
    {α : Type} (B : Nat) (rank : α → Nat)
    (step : α → α → Prop) (terminal : α → Prop)
    (hbound : ∀ x, rank x ≤ B)
    (hstep : ∀ x, ¬ terminal x → ∃ y, step x y ∧ rank x < rank y) :
    ∀ x, ∃ y, Relation.ReflTransGen step x y ∧ terminal y := by sorry
