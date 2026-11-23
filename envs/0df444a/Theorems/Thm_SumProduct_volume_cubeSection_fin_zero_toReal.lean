-- Prove2me | Theorems.Thm_SumProduct_volume_cubeSection_fin_zero_toReal
-- name    : SumProduct.volume_cubeSection_fin_zero_toReal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:57:03.040335+00:00
-- url     : https://prove2.me/theorems/5a2f44aa-d526-467e-8763-20f8990c495b
-- title:
--   Sum Product: volume cube Section fin zero to Real
-- statement:
--   The zero-dimensional cube section is the whole (one-point) space, of volume `1`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionHensley.lean#L22-L28
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionHensley.lean#L22-L28

import Definitions.Def_SumProduct_CubeSectionCore
import Definitions.Def_SumProduct_CubeSectionHensley
set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct

theorem SumProduct.volume_cubeSection_fin_zero_toReal :
    (volume (cubeSection (Fin 0) 1)).toReal = 1 := by sorry
