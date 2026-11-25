-- Prove2me | Theorems.Thm_SCCThm8_realize_aux
-- name    : SCCThm8.realize_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:21.196327+00:00
-- url     : https://prove2.me/theorems/dc3d3ad0-3718-483e-aa89-621c9e072b36
-- title:
--   SCCThm8: realize aux
-- statement:
--   Incremental round-robin dealing: for any finset `s` and multiplicities `m ≤ 3`, there are
--   subsets `A, B, C ⊆ s` of sizes `⌈N/3⌉, ⌈(N-1)/3⌉, ⌊N/3⌋` (where `N = ∑_{s} m`) realizing `m`.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L19-L64
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L19-L64

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset

theorem SCCThm8.realize_aux {α : Type*} [DecidableEq α] (m : α → ℕ) (hm : ∀ i, m i ≤ 3)
    (s : Finset α) :
    ∃ A B C : Finset α, A ⊆ s ∧ B ⊆ s ∧ C ⊆ s ∧
      A.card = (∑ i ∈ s, m i + 2) / 3 ∧ B.card = (∑ i ∈ s, m i + 1) / 3 ∧
      C.card = (∑ i ∈ s, m i) / 3 ∧
      ∀ i ∈ s, (if i ∈ A then 1 else 0) + (if i ∈ B then 1 else 0) +
        (if i ∈ C then 1 else 0) = m i := by sorry
