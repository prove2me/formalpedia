-- Prove2me | Theorems.Thm_TaoFivePrimes_goldbach_blocks_tile_range
-- name    : TaoFivePrimes.goldbach_blocks_tile_range
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-23T16:12:36.293006+00:00
-- url     : https://prove2.me/theorems/dd25e739-0ace-402f-ab2f-88f1749752ab
-- title:
--   The one-million blocks tile the Richstein interval [4, 4·10¹⁴]
-- statement:
--   For every $n$ with $4 \le n \le 4\cdot 10^{14}$ there is a block index $0 \le b < 400{,}000{,}001$ with $\max(4, b\cdot 10^6) \le n \le \min(4\cdot 10^{14}, (b+1)\cdot 10^6 - 1)$.
--
--   This is the tiling fact that lets per-block finite checks (as in `Richstein2001.segmented_sieve_coverage`, whose block geometry is reused verbatim here) assemble into a statement about the whole interval $[4, 4\cdot 10^{14}]$: the blocks $[b\cdot 10^6, (b+1)\cdot 10^6)$ for $b < 400{,}000{,}001$, clipped to $[4, 4\cdot 10^{14}]$, cover the interval. The witness is $b = \lfloor n / 10^6 \rfloor$; the verification is pure integer arithmetic.
-- source:
--   Five-primes mission; decomposes TaoFivePrimes.even_goldbach_verified (5247b31b-05f6-40f5-87b2-e5ce7b0e51f3). Block geometry (width 10⁶, 400,000,001 blocks) mirrors Richstein2001.segmented_sieve_coverage (73281223-e520-4706-9186-a986548dc0d1).

import Mathlib

set_option autoImplicit false

namespace TaoFivePrimes

theorem goldbach_blocks_tile_range (n : ℕ) (hlo : 4 ≤ n) (hhi : n ≤ 4 * 10 ^ 14) :
    ∃ b : ℕ, b < 400000001 ∧
      max 4 (b * 1000000) ≤ n ∧ n ≤ min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1) := by sorry
end TaoFivePrimes
