-- Prove2me | Theorems.Thm_SumProduct_floor_ratio_lt_goldenRatio
-- name    : SumProduct.floor_ratio_lt_goldenRatio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:22:18.408264+00:00
-- url     : https://prove2.me/theorems/8a403c22-e530-48c4-9231-bd42cf778edb
-- title:
--   Sum Product: floor ratio lt golden Ratio
-- statement:
--   For `X ≥ 2` and `0 < ε ≤ 3/20`, with `n = ⌊X⌋`, the directness ratio `(n+εX)/(n−εX)` is below
--   `φ` (in fact below `8/5`). This is what lets `card_construction` apply with `r = εX`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/GoldenRatio.lean#L29-L39
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/GoldenRatio.lean#L29-L39

import Mathlib
import Definitions.Def_SumProduct_GoldenRatio
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct

theorem SumProduct.floor_ratio_lt_goldenRatio {X ε : ℝ} (hX : 2 ≤ X) (hε0 : 0 < ε) (hε : ε ≤ 3 / 20) :
    ((⌊X⌋₊ : ℝ) + ε * X) / ((⌊X⌋₊ : ℝ) - ε * X) < Real.goldenRatio := by sorry
