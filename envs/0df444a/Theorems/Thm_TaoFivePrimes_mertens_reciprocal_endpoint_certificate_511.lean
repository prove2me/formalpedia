-- Prove2me | Theorems.Thm_TaoFivePrimes_mertens_reciprocal_endpoint_certificate_511
-- name    : TaoFivePrimes.mertens_reciprocal_endpoint_certificate_511
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-27T22:44:45.545811+00:00
-- url     : https://prove2.me/theorems/91d4c464-b275-4e79-a699-54ab81854cb4
-- title:
--   Finite endpoint certificate for the reciprocal-prime estimate below 512
-- statement:
--   Let $B=\gamma+\sum_p(\log(1-1/p)+1/p)$ be the Meissel–Mertens constant. For every integer $2\le n\le511$,
--
--   $$\sum_{p\le n}\frac1p\le\log\log n+B+\frac4{\log^3(n+1)}.$$
--
--   The use of $n+1$ in the correction term makes this a sufficient finite endpoint certificate for every real point in $[n,n+1)$. This is a concrete 510-case numerical certificate, not an assertion that the finite verification has been completed.
-- source:
--   Finite endpoint strengthening, introduced for the reduction of TaoFivePrimes.mawia_reciprocal_sum_upper_bound_small. The parent is the Mawia reciprocal-prime estimate; this numerical certificate is an auxiliary obligation, not a quoted theorem from Mawia.

import Mathlib

theorem TaoFivePrimes.mertens_reciprocal_endpoint_certificate_511 (n : ℕ) (hn : 2 ≤ n) (hN : n ≤ 511) :
    (∑ p ∈ Nat.primesLE n, 1 / (p : ℝ)) ≤
      Real.log (Real.log (n : ℝ)) +
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
        4 / (Real.log ((n : ℝ) + 1)) ^ 3 := by sorry
