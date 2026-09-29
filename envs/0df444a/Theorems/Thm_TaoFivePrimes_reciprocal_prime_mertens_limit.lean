-- Prove2me | Theorems.Thm_TaoFivePrimes_reciprocal_prime_mertens_limit
-- name    : TaoFivePrimes.reciprocal_prime_mertens_limit
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:58:53.111636+00:00
-- url     : https://prove2.me/theorems/415d7119-0292-4cbd-9e1f-bc7d99cde221
-- title:
--   Mertens limit with the exact Euler-product constant
-- statement:
--   The reciprocal-prime sum has the limit
--   $$\lim_{x\to\infty}\left(\sum_{p\le x}\frac1p-\log\log x\right)=\gamma+\sum_p\left(\log(1-1/p)+1/p\right).$$
--   The right side explicitly identifies the Meissel–Mertens constant through an absolutely convergent prime series. Unlike an existential version of Mertens' second theorem, this statement identifies the constant needed to convert finite Abel summation into the exact theta-tail identity. The accompanying proof adapts the complete formal proof of Mertens' second theorem and constant identification from the PrimeNumberTheoremAnd project.
-- source:
--   PrimeNumberTheoremAnd, revision 55270df807213fc3584523d09e0311d7dc073ff5, PrimeNumberTheoremAnd/IEANTN/Mertens.lean, Mertens.E₂p.bound' and Mertens.M.eq. https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/55270df807213fc3584523d09e0311d7dc073ff5/PrimeNumberTheoremAnd/IEANTN/Mertens.lean. Apache License 2.0.

import Mathlib
open Filter Topology

theorem TaoFivePrimes.reciprocal_prime_mertens_limit :
    Tendsto (fun x : ℝ =>
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) - Real.log (Real.log x))
      atTop (nhds (Real.eulerMascheroniConstant +
        ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))) := by sorry
