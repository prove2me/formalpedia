-- Prove2me | Theorems.Thm_TaoFivePrimes_siftedVonMangoldt_nonneg
-- name    : TaoFivePrimes.siftedVonMangoldt_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-08T08:53:46.237238+00:00
-- url     : https://prove2.me/theorems/e5d6e8d3-1321-46d2-8c2c-5b328dd2137c
-- title:
--   The sifted von Mangoldt weight is nonnegative
-- statement:
--   The sifted von Mangoldt weight $A_N(n) = \Lambda(n)\,\mathbf 1_{(n,\,\sqrt N\sharp)=1}$, which removes from $\Lambda$ every $n$ sharing a prime factor with the primorial of $\sqrt N$, is nonnegative for all $N$ and $n$. It is either $\Lambda(n)$, which is nonnegative, or zero.
--
--   This is the weight appearing in equation (8.10) and, with the modulus $q_0 = \sqrt N \sharp$, in the exponential sums $S_{\eta,q_0}$ that Theorem 1.3 estimates.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, Mathematics of Computation 83 (2014), 997-1038, https://arxiv.org/abs/1201.6656, Section 8, equation (8.10); nonnegativity of the von Mangoldt function is standard.

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount
open TaoFivePrimes

namespace TaoFivePrimes

theorem siftedVonMangoldt_nonneg (N n : ℕ) : 0 ≤ siftedVonMangoldt N n := by
  sorry

end TaoFivePrimes
