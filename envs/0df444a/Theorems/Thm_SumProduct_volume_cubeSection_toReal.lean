-- Prove2me | Theorems.Thm_SumProduct_volume_cubeSection_toReal
-- name    : SumProduct.volume_cubeSection_toReal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:52:04.290797+00:00
-- url     : https://prove2.me/theorems/018a3270-0fd6-42cc-961b-1e0efcafbca9
-- title:
--   Sum Product: volume cube Section to Real
-- statement:
--   Real-valued homogeneity: `vol(cubeSection ι r).toReal = r ^ n · vol(cubeSection ι 1).toReal`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSection.lean#L125-L128
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSection.lean#L125-L128

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_CubeSection
set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
variable {ι : Type*} [Fintype ι]

theorem SumProduct.volume_cubeSection_toReal (r : ℝ) (hr : 0 ≤ r) :
    (volume (cubeSection ι r)).toReal
      = r ^ Fintype.card ι * (volume (cubeSection ι 1)).toReal := by sorry
