-- Prove2me | Theorems.Thm_SumProduct_integrable_sinc_pow
-- name    : SumProduct.integrable_sinc_pow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:57:32.667705+00:00
-- url     : https://prove2.me/theorems/ba54bcad-1301-45d9-bf69-3a0534282157
-- title:
--   Sum Product: integrable sinc pow
-- statement:
--   The integrand `(sinc t) ^ N` is integrable for `N ≥ 2`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/SincIntegral.lean#L73-L80
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/SincIntegral.lean#L73-L80

import Mathlib
import Definitions.Def_SumProduct_SincIntegral
set_option autoImplicit true
open MeasureTheory Set
open SumProduct
open Real

theorem SumProduct.integrable_sinc_pow {N : ℕ} (hN : 2 ≤ N) :
    Integrable (fun t : ℝ => (Real.sinc t) ^ N) := by sorry
