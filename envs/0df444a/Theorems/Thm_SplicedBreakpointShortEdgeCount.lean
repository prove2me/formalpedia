-- Prove2me | Theorems.Thm_SplicedBreakpointShortEdgeCount
-- name    : SplicedBreakpointShortEdgeCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:06:02.316511+00:00
-- url     : https://prove2.me/theorems/31e8792e-2b85-4d4e-894f-5e1d5acc8067
-- title:
--   Spliced Breakpoint Short Edge Count: Spliced Breakpoint Short Edge Count
-- statement:
--   Transport of a windowed short-edge count along a *spliced* pair of affine reindexings. The
--   interior breakpoints `sA 1, …, sA (K-1)` are now described in two stretches: a tail stretch
--   `sA i = s (c + (i-1)) + σ` for `1 ≤ i ≤ m`, and a head stretch `sA i = s (i - m) + τ` for
--   `m < i ≤ K-1`, the two meeting at the splice value `sA m = s (c + (m-1)) + σ = τ`, which is where
--   `s` restarts from `s 0 = 0`. The two-piece map `i ↦ if i ≤ m then c + (i-1) else i - m` then sends
--   each short edge of `sA` lying in the window `[a',b']` to a short edge of `s`; the tail stretch
--   lands right of `a' - σ` and the head stretch lands left of `b' - τ`, which is exactly the
--   disjunctive window `(a' - σ ≤ s (j-1) ∨ s j ≤ b' - τ)` of a *circular* window of `s`, and the
--   margin hypothesis `b' - τ < a' - σ` is what forces the two stretches to land on disjoint index
--   ranges, making the map injective across the splice. The window `[a',b']` is an arbitrary parameter,
--   not the extreme window `[sA 1, sA (K-1)]`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SplicedBreakpointShortEdgeCount.lean#L17-L105
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SplicedBreakpointShortEdgeCount.lean#L17-L105

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_SplicedBreakpointShortEdgeCount
set_option autoImplicit false
open Set

theorem SplicedBreakpointShortEdgeCount (k n K c m : ℕ) (δ σ τ a' b' : ℝ) (s sA : ℕ → ℝ)
    (hmonoS : MonotoneOn s (Set.Icc 0 k))
    (hs0 : s 0 = 0) (hm1 : 1 ≤ m) (hmK : m + 2 ≤ K)
    (htail : ∀ i : ℕ, 1 ≤ i → i ≤ m → c + (i - 1) ≤ k ∧ sA i = s (c + (i - 1)) + σ)
    (hhead : ∀ i : ℕ, m < i → i ≤ K - 1 → i - m ≤ k ∧ sA i = s (i - m) + τ)
    (hsplice : s (c + (m - 1)) + σ = τ)
    (hmargin : b' - τ < a' - σ)
    (hcount : ((Finset.Icc 1 k).filter
      (fun j => (a' - σ ≤ s (j - 1) ∨ s j ≤ b' - τ) ∧ s j - s (j - 1) < δ)).card ≤ n) :
    ((Finset.Icc 2 (K - 1)).filter
      (fun i => a' ≤ sA (i - 1) ∧ sA i ≤ b' ∧ sA i - sA (i - 1) < δ)).card ≤ n := by sorry
