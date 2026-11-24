-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_pure_moebius_transfer_bound
-- name    : TaoFivePrimes.theorem51_pure_moebius_transfer_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-29T20:44:21.709542+00:00
-- url     : https://prove2.me/theorems/84ff0eaf-4aa7-435a-a810-dff67fcdb081
-- title:
--   Pure Möbius transfer bound for the Type I slab
-- statement:
--   Under the parameter assumptions of the sharp Type I transfer gap, let $D$ be the odd divisors up to $UV$, let $S_1(d)$ be the full logarithmic slab, and let $S_3$ be the globally summed transferred Möbius block. Put $m_d=|\mu(d)|$ for $d\le\lfloor U\rfloor$ and $m_d=0$ otherwise. The analytic estimate is $$\|S_3\|\le\sum_{d\in D}(1-m_d)\|S_1(d)\|.$$ It retains cancellation across Möbius weighted slabs. The Vaughan correction coefficient is absent; the elementary bound $|f_d|\le\log d$ makes this estimate imply the global cancellation target. This strengthening is proposed here and is not stated separately in the paper.
-- source:
--   Derived analytic subproblem for TaoFivePrimes.theorem51_sharp_transfer_gap_global_cancellation, motivated by Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Section 4, Lemma 4.11, absorption after equation (4.18); this strengthening is not explicitly asserted in the paper.

import Definitions.Def_TaoFivePrimes_TypeISlabSums

open scoped BigOperators

theorem TaoFivePrimes.theorem51_pure_moebius_transfer_bound
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ‖TaoFivePrimes.typeISlabS3 x alpha U V‖ ≤
      ∑ d ∈ TaoFivePrimes.theorem51Divisors U V,
        (1 - ‖(if d ≤ ⌊U⌋₊ then (ArithmeticFunction.moebius d : ℂ) else 0)‖) *
          ‖TaoFivePrimes.typeISlabS1 x alpha d‖ := by sorry
