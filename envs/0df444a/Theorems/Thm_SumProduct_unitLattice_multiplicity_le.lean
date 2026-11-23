-- Prove2me | Theorems.Thm_SumProduct_unitLattice_multiplicity_le
-- name    : SumProduct.unitLattice_multiplicity_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:57:57.425005+00:00
-- url     : https://prove2.me/theorems/bc5abb55-8b09-4cf7-8a7c-3abc292576df
-- title:
--   Sum Product: unit Lattice multiplicity le
-- statement:
--   Pointwise multiplicity bound for the unit lattice: every translate of the radius-`Y/2` box
--   contains at most `#(unitLattice ∩ unitBox Y)` lattice points (difference-set injection).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/MultiplicativeCount.lean#L43-L81
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/MultiplicativeCount.lean#L43-L81

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

theorem SumProduct.unitLattice_multiplicity_le {K : Type*} [Field K] [NumberField K] {Y : ℝ}
    (y : logSpace K) :
    ∑' l : ↥(unitLattice K), (unitBox K (Y / 2)).indicator (fun _ => (1 : ENNReal)) (l +ᵥ y)
      ≤ (↑(unitLattice K) ∩ unitBox K Y).encard := by sorry
