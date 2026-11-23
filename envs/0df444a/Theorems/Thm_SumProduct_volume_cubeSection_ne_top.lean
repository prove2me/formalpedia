-- Prove2me | Theorems.Thm_SumProduct_volume_cubeSection_ne_top
-- name    : SumProduct.volume_cubeSection_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:53:07.073119+00:00
-- url     : https://prove2.me/theorems/63bc99ad-e53a-42e6-84da-2055a99a711e
-- title:
--   Sum Product: volume cube Section ne top
-- statement:
--   `cubeSection ι r` has finite volume (it sits inside a sup-ball of radius `|r|`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSection.lean#L116-L122
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSection.lean#L116-L122

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_CubeSection
set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
variable {ι : Type*} [Fintype ι]

theorem SumProduct.volume_cubeSection_ne_top (r : ℝ) : volume (cubeSection ι r) ≠ ⊤ := by sorry
