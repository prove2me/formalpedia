-- Prove2me | Theorems.Thm_WeilDefect_RPB108_four_column_tail_gap
-- name    : WeilDefect.RPB108.four_column_tail_gap
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T20:14:22.195816+00:00
-- url     : https://prove2.me/theorems/ad347866-c899-4953-9c9f-f13e5fe64265
-- title:
--   Four column tail gap
-- statement:
--   For real arrays $w,L,z$ indexed by the four indices $0,1,2,3$, real numbers $k>0$ and $g\ge0$, and a real number $r\ge0$, assume $L_i>0$ at every index and $g\bigl(\sum_{i=0}^3w_i^2/L_i+1/k\bigr)\le1$. Then $g\bigl(\sum_{i=0}^3w_i|z_i|+r\bigr)^2\le\sum_{i=0}^3L_i z_i^2+kr^2$. The weights and entries may have either sign, including a negative weighted sum; $g=0$ and $r=0$ are allowed. All sums have exactly four terms, and the denominators are precisely the positive $L_i$ and $k$.
-- source:
--   monocap-tech/weil, post-Horizon-1 RPB108 conditional physical-gap library. Immutable native head ada7948cb459fd21d400cd8f2a92e87672e31f2d; CompletedColumns.lean, line 9; SHA256 79e8e4bde2ec62b81ab4dc5b861c03619ff6006496bc610ff2ad24be9d84405e. All defining APIs are standard Mathlib; explicit original-form attachment hypotheses are retained.
--
--   Literature/source audit addendum (COR-23): This is an internally proved general algebra or norm estimate. Its exact graph type matches the native declaration WeilDefect.RPB108.four_column_tail_gap in WeilDefect/RPB108/CompletedColumns.lean at ada7948cb459fd21d400cd8f2a92e87672e31f2d (SHA256 79e8e4bde2ec62b81ab4dc5b861c03619ff6006496bc610ff2ad24be9d84405e). Native bytes were verified against retained Git, and the library declarations were independently checked in Lean; public availability of the pin has not been checked. Any application to the original Weil form retains the supplied form/realization hypotheses. This record does not discharge original-form attachment, global continuation, or RH obligations.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem WeilDefect.RPB108.four_column_tail_gap (w L : Fin 4 → ℝ) (k gap : ℝ)
    (hL : ∀ i, 0 < L i) (hk : 0 < k) (hgap : 0 ≤ gap)
    (hbound : gap * ((∑ i, (w i)^2 / L i) + 1/k) ≤ 1)
    (z : Fin 4 → ℝ) (r : ℝ) (hr : 0 ≤ r) :
    gap * ((∑ i, w i * |z i|) + r)^2 ≤
      (∑ i, L i * (z i)^2) + k*r^2 := by sorry
