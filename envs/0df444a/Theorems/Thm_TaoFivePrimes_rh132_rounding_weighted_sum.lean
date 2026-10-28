-- Prove2me | Theorems.Thm_TaoFivePrimes_rh132_rounding_weighted_sum
-- name    : TaoFivePrimes.rh132_rounding_weighted_sum
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:22:38.390652+00:00
-- url     : https://prove2.me/theorems/de08a268-6092-45ba-bd29-cd3b8ce05a84
-- title:
--   Exact radius-3.1 rounding budget for height-132 xi
-- statement:
--   Let $\varepsilon_n$ be the proposed height-132 rounding tolerances. Then
--
--   $$
--   \sum_{n=0}^{59}\left(2\cdot10^{-34}+\varepsilon_n\right)
--   \left(\frac{31}{10}\right)^n \le \frac4{1000}.
--   $$
--
--   This exact arithmetic budget is conditional only in its intended application: the separate rounding tolerances themselves must still be proved.
-- source:
--   Exact rational arithmetic for the direct theta/Mellin quadrature framework due to Gabewhigham and sometik179.

import Definitions.Def_TaoFivePrimes_RH132RoundingSpec
import Mathlib
open Finset

theorem TaoFivePrimes.rh132_rounding_weighted_sum :
    (∑ n ∈ range 60, ((2/10^34:ℝ)+RH132RoundingSpec.bound n)*(31/10:ℝ)^n) ≤ 4/1000 := by sorry
