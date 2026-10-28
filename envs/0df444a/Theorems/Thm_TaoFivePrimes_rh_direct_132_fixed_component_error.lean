-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_component_error
-- name    : TaoFivePrimes.rh_direct_132_fixed_component_error
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:53:16.511073+00:00
-- url     : https://prove2.me/theorems/99219bc9-88c7-4426-b637-3c6ed11be326
-- title:
--   Real error from a height-132 fixed-point floor
-- statement:
--   Let $R_k$ be the cached direct rule and suppose the stored fixed-point integer satisfies its two floor inequalities. Then its scaled value differs by at most $10^{-90}$ from the real part of $R_k$ when $k$ is even, and from the imaginary part when $k$ is odd. The statement applies to any index satisfying the floor condition.
-- source:
--   Exact finite arithmetic based on the theta/Mellin and quadrature framework of Gabewhigham and sometik179.

import Definitions.Def_TaoFivePrimes_RHDirect132FastNumerator
import Mathlib

theorem TaoFivePrimes.rh_direct_132_fixed_component_error (k : ℕ) (hfloor : RHDirect132FastNumerator.floorHolds k) :
    |(if k%2=0 then (RHDirect132CachedRule.value k).re else (RHDirect132CachedRule.value k).im) -
      (RHDirect132FastNumerator.fixed k:ℝ)/10^90| ≤ 1/10^90 := by sorry
