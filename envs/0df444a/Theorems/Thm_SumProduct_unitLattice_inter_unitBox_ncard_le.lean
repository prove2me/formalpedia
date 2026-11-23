-- Prove2me | Theorems.Thm_SumProduct_unitLattice_inter_unitBox_ncard_le
-- name    : SumProduct.unitLattice_inter_unitBox_ncard_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:58:06.317642+00:00
-- url     : https://prove2.me/theorems/d49ae941-c26d-41be-bd8e-0f99b9a2077b
-- title:
--   Sum Product: unit Lattice inter unit Box ncard le
-- statement:
--   The number of unit-lattice points in `unitBox K Y` is at most `|B^×(Y)|` (they are exactly the
--   image of `B^×(Y)` under the log embedding).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/MultiplicativeCount.lean#L87-L112
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/MultiplicativeCount.lean#L87-L112

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
open MeasureTheory NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem

theorem SumProduct.unitLattice_inter_unitBox_ncard_le {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {Y : ℝ} :
    (↑(unitLattice K) ∩ unitBox K Y).ncard ≤ (boxMult K Y).card := by sorry
