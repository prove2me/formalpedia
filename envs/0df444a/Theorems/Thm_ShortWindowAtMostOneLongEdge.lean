-- Prove2me | Theorems.Thm_ShortWindowAtMostOneLongEdge
-- name    : ShortWindowAtMostOneLongEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:05:51.096805+00:00
-- url     : https://prove2.me/theorems/7fd4bec2-8ee2-4140-91c9-063117819b59
-- title:
--   Short Window At Most One Long Edge: Short Window At Most One Long Edge
-- statement:
--   At most one index of a monotone breakpoint sequence `sA` can carry a long edge inside a short
--   interior window: if `sA` is monotone on `{0,…,K}` and its interior window `[sA 1, sA (K-1)]` has
--   length at most `δ > 0`, then at most one interior index `i ∈ {2,…,K-1}` has
--   `δ ≤ sA i - sA (i-1)`. Two such indices would contribute two disjoint sub-intervals of total
--   length at least `2δ` to a window of length at most `δ`. This is the half of
--   `ArcShortWindowEdgeCount`'s counting that needs no correspondence with the ambient curve: it is a
--   statement about the breakpoint sequence alone. Natural-number subtraction is used throughout, so
--   the index set is empty when `K ≤ 2`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ShortWindowAtMostOneLongEdge.lean#L14-L38
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ShortWindowAtMostOneLongEdge.lean#L14-L38

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_ShortWindowAtMostOneLongEdge
set_option autoImplicit false
open Set

theorem ShortWindowAtMostOneLongEdge (K : ℕ) (sA : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hmono : MonotoneOn sA (Set.Icc 0 K))
    (hshort : sA (K - 1) - sA 1 ≤ δ) :
    ((Finset.Icc 2 (K - 1)).filter (fun i => δ ≤ sA i - sA (i - 1))).card ≤ 1 := by sorry
