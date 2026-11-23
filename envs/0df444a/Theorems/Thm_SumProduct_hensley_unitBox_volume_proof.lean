-- Prove2me | Theorems.Thm_SumProduct_hensley_unitBox_volume_proof
-- name    : SumProduct.hensley_unitBox_volume_proof
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:57:34.804404+00:00
-- url     : https://prove2.me/theorems/be9f0b7c-bc69-49a6-bea4-b68fb701f1fe
-- title:
--   Sum Product: hensley unit Box volume proof
-- statement:
--   **Equation (3.1) as a theorem** (was `hensley_unitBox_volume`): the two-sided volume bound on
--   `unitBox K r`, with the sharp `√d` denominator and constants `1`/`5`, for every totally real `K`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionHensley.lean#L34-L70
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionHensley.lean#L34-L70

import Definitions.Def_SumProduct_CubeSectionCore
import Definitions.Def_SumProduct_CubeSectionHensley
set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
open scoped Classical
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem

theorem SumProduct.hensley_unitBox_volume_proof (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (r : ℝ) (hr : 0 ≤ r) :
    (2 * r) ^ (Module.finrank ℚ K - 1) / Real.sqrt (Module.finrank ℚ K)
        ≤ (volume (unitBox K r)).toReal ∧
      (volume (unitBox K r)).toReal
        ≤ 5 * (2 * r) ^ (Module.finrank ℚ K - 1) / Real.sqrt (Module.finrank ℚ K) := by sorry
