-- Prove2me | Theorems.Thm_SumProduct_hensley_unitBox_volume
-- name    : SumProduct.hensley_unitBox_volume
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:01:51.704386+00:00
-- url     : https://prove2.me/theorems/221cc1a8-b63f-4b20-a708-225cc44476dc
-- title:
--   Sum Product: hensley unit Box volume
-- statement:
--   **Equation (3.1)** (Hensley / Ball–Vaaler cube-slice volume bound), expressed in `logSpace K`:
--   the trace-zero box `unitBox K r ⊂ logSpace K ≅ ℝ^{d-1}` has volume in
--   `[(2r)^{d-1}/√d, 5(2r)^{d-1}/√d]`.
--
--   The public re-export of `hensley_unitBox_volume_proof`.  `unitBox K r`
--   is, definitionally, the sum-constrained cube `cubeSection {w ≠ w₀} r`; its volume reduces
--   (homogeneity + coordinate relabeling) to the 1-D law of a sum of `d-1` independent uniforms on
--   `[-1,1]`, whose interval probability is identified by Fourier inversion with `(1/π)∫ (sin t/t)^d`,
--   and bounded by the elementary estimate `π/√d ≤ ∫ (sin t/t)^d ≤ 5π/√d`. (No appeal to Vaaler/Ball;
--   the elementary sinc-integral bound suffices for the stated constants.)
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionHensley.lean#L84-L90
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSectionHensley.lean#L84-L90

import Definitions.Def_SumProduct_CubeSectionCore
import Definitions.Def_SumProduct_CubeSectionHensley
set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
open scoped Classical
open MeasureTheory NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem

theorem SumProduct.hensley_unitBox_volume (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (r : ℝ) (hr : 0 ≤ r) :
    (2 * r) ^ (Module.finrank ℚ K - 1) / Real.sqrt (Module.finrank ℚ K)
        ≤ (volume (unitBox K r)).toReal ∧
      (volume (unitBox K r)).toReal
        ≤ 5 * (2 * r) ^ (Module.finrank ℚ K - 1) / Real.sqrt (Module.finrank ℚ K) := by sorry
