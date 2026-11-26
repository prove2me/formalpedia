-- Prove2me | Theorems.Thm_ShiftedBreakpointShortEdgeCount
-- name    : ShiftedBreakpointShortEdgeCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:05:18.551904+00:00
-- url     : https://prove2.me/theorems/451b9dfb-9e83-5783-9aba-4e42447f3176
-- title:
--   Shifted Breakpoint Short Edge Count: Shifted Breakpoint Short Edge Count
-- statement:
--   Transport of a windowed short-edge count along an affine reindexing of breakpoints. If the
--   breakpoints `sA i` for `i` in an index range `{p-1,…,q}` are obtained from those of a second
--   sequence `s` by a single index map `i ↦ i + c - d` (with `d + 1 ≤ p + c`, so no natural-number
--   truncation occurs on the range) and a single value shift `σ`, namely `sA i = s (i + c - d) + σ`
--   with `i + c - d ≤ k`, then each index `i ∈ {p,…,q}` whose edge `sA i - sA (i-1)` is shorter than
--   `δ` and which lies in the window `[a',b']` (i.e. `a' ≤ sA (i-1)` and `sA i ≤ b'`) maps, under
--   `i ↦ i + c - d`, to an index `j ∈ {1,…,k}` whose edge `s j - s (j-1)` is shorter than `δ` and
--   which lies in the shifted window `[a'-σ, b'-σ]`. Since that map is injective, any bound `n` on the
--   number of such `j` bounds the number of such `i`. The window `[a',b']` is an arbitrary parameter,
--   not the extreme window `[sA 1, sA (K-1)]`, which is what lets a consumer count inside a small
--   sub-window of a long breakpoint sequence.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ShiftedBreakpointShortEdgeCount.lean#L17-L46
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ShiftedBreakpointShortEdgeCount.lean#L17-L46

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_ShiftedBreakpointShortEdgeCount
set_option autoImplicit false
open Set

theorem ShiftedBreakpointShortEdgeCount (k n p q c d : ℕ) (δ σ a' b' : ℝ) (s sA : ℕ → ℝ)
    (hp : 1 ≤ p) (hd : d + 1 ≤ p + c)
    (hcorr : ∀ i : ℕ, p - 1 ≤ i → i ≤ q → i + c - d ≤ k ∧ sA i = s (i + c - d) + σ)
    (hcount : ((Finset.Icc 1 k).filter
      (fun j => a' - σ ≤ s (j - 1) ∧ s j ≤ b' - σ ∧ s j - s (j - 1) < δ)).card ≤ n) :
    ((Finset.Icc p q).filter
      (fun i => a' ≤ sA (i - 1) ∧ sA i ≤ b' ∧ sA i - sA (i - 1) < δ)).card ≤ n := by sorry
