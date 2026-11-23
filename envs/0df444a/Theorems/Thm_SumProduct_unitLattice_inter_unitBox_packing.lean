-- Prove2me | Theorems.Thm_SumProduct_unitLattice_inter_unitBox_packing
-- name    : SumProduct.unitLattice_inter_unitBox_packing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:58:41.336271+00:00
-- url     : https://prove2.me/theorems/16d7563d-7448-44ae-a0e7-bd7791c825ea
-- title:
--   Sum Product: unit Lattice inter unit Box packing
-- statement:
--   **Packing bound** for the Lemma 3.7 upper estimate:
--   `#(unitLattice ∩ unitBox Y) ≤ 5(5Y+1)^{d-1}`. Disjoint translates of `unitBox(1/5)` (disjoint by
--   `unitLattice_unitBox_eq_zero`) pack into `unitBox(Y+1/5)`; eq (3.1) bounds the volumes, and the
--   constants work out exactly with radius `1/5`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/MultiplicativeCount.lean#L291-L363
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/MultiplicativeCount.lean#L291-L363

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

theorem SumProduct.unitLattice_inter_unitBox_packing {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {d : ℕ} (hd : Module.finrank ℚ K = d) (Y : ℝ) (hY : 1 ≤ Y) :
    ((↑(unitLattice K) ∩ unitBox K Y).ncard : ℝ) ≤ 5 * (5 * Y + 1) ^ (d - 1) := by sorry
