-- Prove2me | Theorems.Thm_StraddleAtMostOneEdge
-- name    : StraddleAtMostOneEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:09:24.010382+00:00
-- url     : https://prove2.me/theorems/883bed74-42fe-5bee-a708-b0a18f1cbb95
-- title:
--   Straddle At Most One Edge: Straddle At Most One Edge
-- statement:
--   Edges of a monotone breakpoint sequence have pairwise disjoint interiors, so a single real
--   number `c` lies in the open interior `(s (j-1), s j)` of at most one edge `j ∈ {1,…,k}`.
--   Natural-number subtraction is used for `j - 1`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/StraddleAtMostOneEdge.lean#L9-L28
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/StraddleAtMostOneEdge.lean#L9-L28

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_StraddleAtMostOneEdge
set_option autoImplicit false
open Set

theorem StraddleAtMostOneEdge (k : ℕ) (s : ℕ → ℝ) (c : ℝ)
    (hmono : MonotoneOn s (Set.Icc 0 k)) :
    ((Finset.Icc 1 k).filter (fun j => s (j - 1) < c ∧ c < s j)).card ≤ 1 := by sorry
