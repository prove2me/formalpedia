-- Prove2me | Theorems.Thm_RectangleErrorTradeoff_diagonal_sq_le
-- name    : RectangleErrorTradeoff.diagonal_sq_le
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T21:23:57.817852+00:00
-- url     : https://prove2.me/theorems/74c7bdd6-7540-5277-95ee-ca76d4b3f4cb
-- title:
--   A quadratic tradeoff between diagonal coverage and off-diagonal errors
-- statement:
--   Let a union of k rectangles on X times X cover each marked diagonal entry (x,x), with m distinct marked points x. Let a finite set of b pairs include every covered off-diagonal pair between marked points. Then m squared is at most k times (m+b). The count is of ordered pairs and the inequality includes the case of zero rectangles.
-- source:
--   The communication-complexity rectangle bound with a counting argument for collisions and the Cauchy-Schwarz inequality. Standard zero-error rectangle framework: Yao, Some complexity questions related to distributive computing, STOC 1979, https://doi.org/10.1145/800135.804414.

import Mathlib

theorem RectangleErrorTradeoff.diagonal_sq_le {A I : Type*} [DecidableEq A] [Fintype I]
    (left right : I → A → Prop) (diag : Finset A) (bad : Finset (A × A))
    (positive : ∀ a ∈ diag, (∃ i, left i a ∧ right i a))
    (includesErrors : ∀ a ∈ diag, ∀ b ∈ diag,
      a ≠ b → (∃ i, left i a ∧ right i b) → (a,b) ∈ bad) :
    diag.card^2 ≤ Fintype.card I * (diag.card + bad.card) := by sorry
