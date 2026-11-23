-- Prove2me | Theorems.Thm_SumProduct_boxMult_card_le
-- name    : SumProduct.boxMult_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:59:39.37155+00:00
-- url     : https://prove2.me/theorems/f8842c46-2f8d-4a39-b5f1-22cda8638276
-- title:
--   Sum Product: box Mult card le
-- statement:
--   **Upper bound of Lemma 3.7**: `|B^×(Y)| ≤ 10(5Y+1)^{d-1}` (fibration `×2` over the torsion
--   `{±1}`, then the packing bound on the lattice points).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/MultiplicativeCount.lean#L396-L410
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/MultiplicativeCount.lean#L396-L410

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

theorem SumProduct.boxMult_card_le {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {d : ℕ} (hd : Module.finrank ℚ K = d) (Y : ℝ) (hY : 1 ≤ Y) :
    ((boxMult K Y).card : ℝ) ≤ 10 * (5 * Y + 1) ^ (d - 1) := by sorry
