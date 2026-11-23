-- Prove2me | Theorems.Thm_SumProduct_dedekindZeta_completed_ge_residue
-- name    : SumProduct.dedekindZeta_completed_ge_residue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:02:43.21535+00:00
-- url     : https://prove2.me/theorems/fb1d4fca-0406-4d1c-96be-85a6a6ad8f6e
-- title:
--   Sum Product: dedekind Zeta completed ge residue
-- statement:
--   **Completed-zeta residue inequality**: summing the per-class residue inequality over ideal
--   classes gives, for real `s > 1`, that the completed zeta
--   times `s(s-1)` is at least its residue:
--   `κ_K√|Δ_K|/π^{r₂} ≤ s(s-1)·Z_K(s)`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/RegulatorBound.lean#L61-L105
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/RegulatorBound.lean#L61-L105

import Definitions.Def_SumProduct_PartialZetaMellin
import Definitions.Def_SumProduct_MultiplicativeCount
import Definitions.Def_SumProduct_EulerBound
import Definitions.Def_SumProduct_RegulatorBound
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField MeasureTheory NumberField.InfinitePlace

theorem SumProduct.dedekindZeta_completed_ge_residue (K : Type*) [Field K] [NumberField K]
    (s : ℝ) (hs : 1 < s) :
    NumberField.dedekindZeta_residue K * Real.sqrt |(NumberField.discr K : ℝ)|
          / Real.pi ^ nrComplexPlaces K
      ≤ s * (s - 1) * |(NumberField.discr K : ℝ)| ^ (s / 2)
          * (Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2)) ^ nrRealPlaces K
          * (2 * (2 * Real.pi) ^ (-s) * Real.Gamma s) ^ nrComplexPlaces K
          * (NumberField.dedekindZeta K (s : ℂ)).re := by sorry
