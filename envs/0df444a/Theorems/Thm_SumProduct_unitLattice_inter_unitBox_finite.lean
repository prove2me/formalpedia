-- Prove2me | Theorems.Thm_SumProduct_unitLattice_inter_unitBox_finite
-- name    : SumProduct.unitLattice_inter_unitBox_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:04:37.953518+00:00
-- url     : https://prove2.me/theorems/f806a7c1-91eb-4cfe-89f5-0501ee9f4596
-- title:
--   Sum Product: unit Lattice inter unit Box finite
-- statement:
--   The unit-lattice points inside `unitBox K Y` form a finite set (discreteness + boundedness).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/MultiplicativeCount.lean#L29-L37
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/MultiplicativeCount.lean#L29-L37

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
open MeasureTheory NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem Metric

theorem SumProduct.unitLattice_inter_unitBox_finite {K : Type*} [Field K] [NumberField K] {Y : ℝ}
    (hY : 0 ≤ Y) : (↑(unitLattice K) ∩ unitBox K Y).Finite := by sorry
