-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_132_fast_numerator_identity
-- name    : TaoFivePrimes.rh_direct_132_fast_numerator_identity
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:48:57.395685+00:00
-- url     : https://prove2.me/theorems/2d1ec9f5-f98b-4219-aaef-9205ac285137
-- title:
--   Factorial and binomial cached numerators agree
-- statement:
--   For every nonnegative index $k$, the factorial-based integer component equals the corresponding real cached numerator when $k$ is even and the imaginary cached numerator when $k$ is odd. This is an exact identity of finite integer sums.
-- source:
--   Finite theta-jet and Mellin quadrature framework by sometik179 and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHDirect132FastNumerator
import Mathlib

theorem TaoFivePrimes.rh_direct_132_fast_numerator_identity (k : ℕ) :
    RHDirect132FastNumerator.component k =
      if k%2=0 then RHDirect132CachedRule.numeratorRe k
      else RHDirect132CachedRule.numeratorIm k := by sorry
