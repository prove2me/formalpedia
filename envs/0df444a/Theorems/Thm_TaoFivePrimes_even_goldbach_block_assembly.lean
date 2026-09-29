-- Prove2me | Theorems.Thm_TaoFivePrimes_even_goldbach_block_assembly
-- name    : TaoFivePrimes.even_goldbach_block_assembly
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-23T16:12:28.417872+00:00
-- url     : https://prove2.me/theorems/ec9f9a1f-2aa4-403f-8e22-f419dd8817e4
-- title:
--   Assembly: per-block Goldbach witnesses imply the verified even Goldbach statement
-- statement:
--   Assume that for every block index $0 \le b < 400{,}000{,}001$, each even $n$ in the clipped block $[\max(4, b\cdot 10^6),\, \min(4\cdot 10^{14}, (b+1)\cdot 10^6 - 1)]$ is a sum of two primes. Then every even $n$ with $4 \le n \le 4\cdot 10^{14}$ is a sum of two primes.
--
--   This is the final assembly step of the decomposition of `TaoFivePrimes.even_goldbach_verified`: the hypothesis is exactly what the sieve-coverage node `Richstein2001.segmented_sieve_coverage` yields once its survivors are promoted to primes (`TaoFivePrimes.goldbach_sieve_witness_to_primes`), and the conclusion is `even_goldbach_verified` itself. The proof locates the block containing $n$ (`TaoFivePrimes.goldbach_blocks_tile_range`) and applies the hypothesis.
-- source:
--   Five-primes mission; decomposes TaoFivePrimes.even_goldbach_verified (5247b31b-05f6-40f5-87b2-e5ce7b0e51f3). Conclusion restates even_goldbach_verified; hypothesis is the post-sieve per-block form of Richstein2001.segmented_sieve_coverage (73281223-e520-4706-9186-a986548dc0d1).

import Mathlib

set_option autoImplicit false

namespace TaoFivePrimes

theorem even_goldbach_block_assembly
    (hcov : ∀ b : ℕ, b < 400000001 →
      ∀ n : ℕ, max 4 (b * 1000000) ≤ n → n ≤ min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1) →
        Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n)
    (n : ℕ) (h4 : 4 ≤ n) (hN : n ≤ 4 * 10 ^ 14) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by sorry
end TaoFivePrimes
