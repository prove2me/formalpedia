-- Prove2me | Theorems.Thm_SubResolutionShortEdgeCount
-- name    : SubResolutionShortEdgeCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:12:47.233592+00:00
-- url     : https://prove2.me/theorems/c11027c5-09a7-49ec-b62a-16a564807757
-- title:
--   Sub Resolution Short Edge Count: Sub Resolution Short Edge Count
-- statement:
--   **Short-edge counts transport exactly along the shifted sub-resolution `j ↦ s (c+j) - s c`.**
--   `RestrictPiecewiseGeodesic` resolves the window `γ|_{[s c, s d]}` of a curve by the shifted,
--   re-based breakpoint sequence `j ↦ s (c+j) - s c` with `d - c` edges. This lemma says that the
--   number of short (length `< δ`) edges of that sub-resolution is *exactly* the number of short edges
--   of `s` whose index lies in `{c+1,…,d}`: the reindexing `j ↦ c + j` is a bijection
--   `{1,…,d-c} → {c+1,…,d}` and the common base point `s c` cancels out of every edge difference.
--   Unlike `ShiftedBreakpointShortEdgeCount` and `SplicedBreakpointShortEdgeCount`, which are
--   *windowed inequalities* (they bound a count inside a metric window `[a',b']` by a count of `s`),
--   this is an unconditional *identity* of unwindowed counts, which is what is needed to add up the
--   counts of several sub-resolutions and compare the total against `s`'s own count.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SubResolutionShortEdgeCount.lean#L16-L40
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SubResolutionShortEdgeCount.lean#L16-L40

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_SubResolutionShortEdgeCount
set_option autoImplicit false
open Set

theorem SubResolutionShortEdgeCount (c d : ℕ) (s : ℕ → ℝ) (δ : ℝ) :
    ((Finset.Icc 1 (d - c)).filter
        (fun j => (s (c + j) - s c) - (s (c + (j - 1)) - s c) < δ)).card
      = ((Finset.Ioc c d).filter (fun i => s i - s (i - 1) < δ)).card := by sorry
