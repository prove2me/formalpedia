-- Prove2me | Theorems.Thm_SumProduct_lattice_count_mult
-- name    : SumProduct.lattice_count_mult
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:59:52.124329+00:00
-- url     : https://prove2.me/theorems/cb49de64-a8b4-47df-ad0c-6108b3fd03c5
-- title:
--   Sum Product: lattice count mult
-- statement:
--   **Lemma 3.7** (`lem-ball-mult`, multiplicative lattice-point count), now PROVED:
--   `Y^{d-1}/(√d·R_K) ≤ |B^×(Y)| ≤ 10(5Y+1)^{d-1}` for totally real `K` of degree `d` and `Y ≥ 1`.
--   The lower bound is Blichfeldt in the unit lattice (`boxMult_card_ge`); the upper bound is the
--   `{±1}`-fibration over the packing bound (`boxMult_card_le`). The only analytic input is eq (3.1)
--   (`hensley_unitBox_volume`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/MultiplicativeCount.lean#L417-L421
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/MultiplicativeCount.lean#L417-L421

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

theorem SumProduct.lattice_count_mult (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (d : ℕ) (hd : Module.finrank ℚ K = d) (Y : ℝ) (hY : 1 ≤ Y) :
    Y ^ (d - 1) / (Real.sqrt d * NumberField.Units.regulator K) ≤ (boxMult K Y).card ∧
      ((boxMult K Y).card : ℝ) ≤ 10 * (5 * Y + 1) ^ (d - 1) := by sorry
