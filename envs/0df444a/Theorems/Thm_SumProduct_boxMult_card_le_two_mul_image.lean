-- Prove2me | Theorems.Thm_SumProduct_boxMult_card_le_two_mul_image
-- name    : SumProduct.boxMult_card_le_two_mul_image
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:58:34.726546+00:00
-- url     : https://prove2.me/theorems/c7c28b4b-8582-4f1f-a5d6-ea1a8e134b2d
-- title:
--   Sum Product: box Mult card le two mul image
-- statement:
--   `|B^×(Y)| ≤ 2 · #(its log-embedding image)`: every fibre of the log embedding is a coset of
--   the torsion subgroup `{±1}`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/MultiplicativeCount.lean#L221-L248
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/MultiplicativeCount.lean#L221-L248

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_Blichfeldt
import Definitions.Def_SumProduct_UnitSeparation
import Definitions.Def_SumProduct_GoldenRatio
import Definitions.Def_SumProduct_CubeSectionHensley
import Definitions.Def_SumProduct_MultiplicativeCount
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem

theorem SumProduct.boxMult_card_le_two_mul_image {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {Y : ℝ} :
    (boxMult K Y).card
      ≤ 2 * ((boxMult K Y).image (fun u => logEmbedding K (Additive.ofMul u))).card := by sorry
