-- Prove2me | Theorems.Thm_SumProduct_boxMult_card_ge
-- name    : SumProduct.boxMult_card_ge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:58:18.550592+00:00
-- url     : https://prove2.me/theorems/2cb75b1e-bdfc-4753-a0b6-f3f3259d1467
-- title:
--   Sum Product: box Mult card ge
-- statement:
--   **Lower bound of Lemma 3.7** (Blichfeldt in the unit lattice). For a totally real field of
--   degree `d` and `Y ≥ 1`, `Y^{d-1} / (√d · R_K) ≤ |B^×(Y)|`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/MultiplicativeCount.lean#L118-L178
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/MultiplicativeCount.lean#L118-L178

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

theorem SumProduct.boxMult_card_ge {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (d : ℕ) (hd : Module.finrank ℚ K = d) (Y : ℝ) (hY : 1 ≤ Y) :
    Y ^ (d - 1) / (Real.sqrt d * NumberField.Units.regulator K) ≤ (boxMult K Y).card := by sorry
