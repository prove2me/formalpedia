-- Prove2me | Theorems.Thm_SumProduct_volume_pi_Ioo_const
-- name    : SumProduct.volume_pi_Ioo_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:51:32.335119+00:00
-- url     : https://prove2.me/theorems/a2ccb00e-723f-4351-b9f6-3f092479f9e7
-- title:
--   Sum Product: volume pi Ioo const
-- statement:
--   Volume of an axis-aligned cube of side `b − a` in the embedding space `InfinitePlace K → ℝ`
--   (dimension `d`): `(b − a)^d`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L98-L104
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L98-L104

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open MeasureTheory NumberField NumberField.InfinitePlace

theorem SumProduct.volume_pi_Ioo_const {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {d : ℕ} (hd : Module.finrank ℚ K = d) {a b : ℝ} (hab : a ≤ b) :
    volume (Set.univ.pi fun _ : InfinitePlace K => Set.Ioo a b) = ENNReal.ofReal ((b - a) ^ d) := by sorry
