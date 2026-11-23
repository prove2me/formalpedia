-- Prove2me | Theorems.Thm_SumProduct_unitBox_inter_eq_image
-- name    : SumProduct.unitBox_inter_eq_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:59:01.816637+00:00
-- url     : https://prove2.me/theorems/328255d5-691a-43c0-b859-23921c2013ef
-- title:
--   Sum Product: unit Box inter eq image
-- statement:
--   The unit-lattice points in `unitBox Y` are exactly the log-embedding image of `B^×(Y)`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/MultiplicativeCount.lean#L368-L390
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/MultiplicativeCount.lean#L368-L390

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

theorem SumProduct.unitBox_inter_eq_image {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {Y : ℝ} :
    ↑(unitLattice K) ∩ unitBox K Y
      = ↑((boxMult K Y).image (fun u => logEmbedding K (Additive.ofMul u))) := by sorry
