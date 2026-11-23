-- Prove2me | Theorems.Thm_SumProduct_sinc_power_integral_bounds
-- name    : SumProduct.sinc_power_integral_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:52:38.900415+00:00
-- url     : https://prove2.me/theorems/0b9e61c6-e816-4837-8139-282baf2e5205
-- title:
--   Sum Product: sinc power integral bounds
-- statement:
--   The Sum Product construction uses the sinc power integral bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/SincIntegral.lean#L803-L806
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/SincIntegral.lean#L803-L806

import Mathlib
import Definitions.Def_SumProduct_SincIntegral
set_option autoImplicit true
open MeasureTheory Set
open SumProduct
open Real

theorem SumProduct.sinc_power_integral_bounds (N : ℕ) (hN : 2 ≤ N) :
    Real.pi / Real.sqrt (N : ℝ) ≤ ∫ t : ℝ, (Real.sinc t) ^ N ∧
      ∫ t : ℝ, (Real.sinc t) ^ N ≤ 5 * Real.pi / Real.sqrt (N : ℝ) := by sorry
