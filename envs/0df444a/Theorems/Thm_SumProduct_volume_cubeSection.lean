-- Prove2me | Theorems.Thm_SumProduct_volume_cubeSection
-- name    : SumProduct.volume_cubeSection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:51:56.60311+00:00
-- url     : https://prove2.me/theorems/6bb5b9fe-7777-4d82-ad3e-8c00f5c94ba7
-- title:
--   Sum Product: volume cube Section
-- statement:
--   The volume scales by `r ^ n` where `n = card ι` (homogeneity of degree `n`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSection.lean#L108-L113
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSection.lean#L108-L113

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_CubeSection
set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
variable {ι : Type*} [Fintype ι]

theorem SumProduct.volume_cubeSection (r : ℝ) (hr : 0 ≤ r) :
    volume (cubeSection ι r)
      = ENNReal.ofReal (r ^ Fintype.card ι) * volume (cubeSection ι 1) := by sorry
