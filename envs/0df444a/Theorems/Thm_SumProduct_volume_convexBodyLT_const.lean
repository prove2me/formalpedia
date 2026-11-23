-- Prove2me | Theorems.Thm_SumProduct_volume_convexBodyLT_const
-- name    : SumProduct.volume_convexBodyLT_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:51:01.142943+00:00
-- url     : https://prove2.me/theorems/28cec234-9889-40a5-91a3-77480055a302
-- title:
--   Sum Product: volume convex Body LT const
-- statement:
--   Volume of the open box `{x : mixedSpace K | ∀ w, normAtPlace w x < r}` for a totally real
--   field of degree `d`: it is `(2r)^d`. This is the box used in the Blichfeldt lower bound.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L110-L120
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L110-L120

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open MeasureTheory NumberField NumberField.mixedEmbedding NumberField.InfinitePlace

theorem SumProduct.volume_convexBodyLT_const {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {d : ℕ} (hd : Module.finrank ℚ K = d) (r : NNReal) :
    volume (convexBodyLT K (fun _ => r)) = (2 : ENNReal) ^ d * (r : ENNReal) ^ d := by sorry
