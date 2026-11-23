-- Prove2me | Theorems.Thm_SumProduct_regulator_le_discr
-- name    : SumProduct.regulator_le_discr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:02:55.886061+00:00
-- url     : https://prove2.me/theorems/b982eb91-fabd-45e2-92be-62b7467b1240
-- title:
--   Sum Product: regulator le discr
-- statement:
--   **Lemma 3.1** (regulator ≤ discriminant), PROVED. For a totally real number field `K` of
--   degree `d ≥ 2`, `R_K ≤ |Δ_K|`. From `dedekind_residue_le` (the functional-equation residue bound
--   at `s = 2`), the analytic class number formula, and `h_K ≥ 1`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/RegulatorBound.lean#L202-L251
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/RegulatorBound.lean#L202-L251

import Definitions.Def_SumProduct_PartialZetaMellin
import Definitions.Def_SumProduct_MultiplicativeCount
import Definitions.Def_SumProduct_EulerBound
import Definitions.Def_SumProduct_RegulatorBound
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open NumberField NumberField.Units NumberField.InfinitePlace

theorem SumProduct.regulator_le_discr (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (hd : 2 ≤ Module.finrank ℚ K) :
    NumberField.Units.regulator K ≤ |(NumberField.discr K : ℝ)| := by sorry
