-- Prove2me | Theorems.Thm_ValiantBorder_priceMidpointCN
-- name    : ValiantBorder.priceMidpointCN
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:03:42.326341+00:00
-- url     : https://prove2.me/theorems/5752039e-2d6b-4e24-9746-c95288c4f68a
-- title:
--   Squared-distance inequality at a midpoint of a price
-- statement:
--   Let $w$ be a price over a field. If $w(x,v)=2D$ and both $w(x,m)$ and $w(v,m)$ are at most $D$, then every point $z$ satisfies $w(z,m)^2≤(w(z,x)^2+w(z,v)^2)/2-D^2$.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Fan.lean#L987).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Fan.lean#L987.

import Definitions.Def_ValiantBorder_fieldCases

theorem ValiantBorder.priceMidpointCN {K : Type} [Field K] {Y : Type} {w : Y → Y → ℝ}
    (hw : Nc.Price.IsPrice K w) (x v m z : Y) {D : ℝ}
    (h1 : w x m ≤ D) (h2 : w v m ≤ D) (h3 : w x v = 2 * D) :
    w z m ^ 2 ≤ 1 / 2 * w z x ^ 2 + 1 / 2 * w z v ^ 2 - D ^ 2 := by sorry
