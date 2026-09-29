-- Prove2me | Theorems.Thm_Rudin_ch05_taylor_helper
-- name    : Rudin.ch05_taylor_helper
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-13T14:38:33.544181+00:00
-- url     : https://prove2.me/theorems/ed62805a-a8c2-4be2-aafb-4deab7c99258
-- title:
--   Helper for Taylor's theorem
-- statement:
--   Helper lemma for Taylor's theorem.

import Mathlib

open Filter Topology

namespace Rudin

theorem ch05_taylor_helper (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (hcont : ContinuousOn (iteratedDeriv (n - 1) f) (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ (iteratedDeriv (n - 1) f) t)
    (α β : ℝ) (hα : α ∈ Set.Icc a b) (hβ : β ∈ Set.Icc a b) (hne : α ≠ β) :
    ∃ x : ℝ, ((α < x ∧ x < β) ∨ (β < x ∧ x < α)) ∧
      f β = (∑ k ∈ Finset.range n, iteratedDeriv k f α / (k.factorial : ℝ) * (β - α) ^ k)
        + iteratedDeriv n f x / (n.factorial : ℝ) * (β - α) ^ n := by sorry

end Rudin
