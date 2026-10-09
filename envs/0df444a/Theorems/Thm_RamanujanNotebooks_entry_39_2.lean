-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_39_2
-- name    : RamanujanNotebooks.entry_39_2
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-07T08:29:12.459825+00:00
-- url     : https://prove2.me/theorems/da9804fc-f96a-41ee-b562-0e2862455ca5
-- title:
--   Integral over the positive axis of the n-th power of sin x / x, as a finite alternating sum
-- statement:
--   Entry 2 of Chapter 39, p. 566. For every positive integer n, the integrals ∫_0^T (sin x / x)^n dx tend, as T → ∞, to π/(2^n (n−1)!) · ∑_{k=0}^{⌊(n−1)/2⌋} ((−n)_k / k!) (n − 2k)^{n−1}, where (−n)_k = (−n)(−n+1)⋯(−n+k−1), so that (−n)_k/k! = (−1)^k C(n,k). Differs from the printed source: the sum is printed with the terms (−n)_k (n − 2k)^{n−1}; here each term is divided by k! (correction ours). With the printed terms the formula gives 5π/16 for n = 5 and 27π/80 for n = 6, while the integrals are 115π/384 and 11π/40; the two readings agree for n ≤ 4. The corrected sum is the classical evaluation π/(2^n (n−1)!) ∑_k (−1)^k C(n,k) (n − 2k)^{n−1} and reproduces the known values for n = 1, …, 8 exactly; the integrals for n = 4, 5, 6 were also computed numerically (numerical evidence, not a proof). The printed sign ±(−1)^n, plus for even n and minus for odd n, equals +1 for every n and is omitted. The integral is stated as the limit of the integrals over [0, T], which for n = 1 is the only sense in which it converges.
--
--   **Discrepancy from the printed source.** Differs from the printed source: the sum is printed with the terms (−n)_k (n − 2k)^{n−1}; here each term is divided by k! (correction ours). With the printed terms the formula gives 5π/16 for n = 5 and 27π/80 for n = 6, while the integrals are 115π/384 and 11π/40; the two readings agree for n ≤ 4. The corrected sum is the classical evaluation π/(2^n (n−1)!) ∑_k (−1)^k C(n,k) (n − 2k)^{n−1} and reproduces the known values for n = 1, …, 8 exactly; the integrals for n = 4, 5, 6 were also computed numerically (numerical evidence, not a proof). The printed sign ±(−1)^n, plus for even n and minus for odd n, equals +1 for every n and is omitted. The integral is stated as the limit of the integrals over [0, T], which for n = 1 is the only sense in which it converges.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part V (Springer, 1998), Chapter 39, Entry 2, p. 566.

import Mathlib

namespace RamanujanNotebooks
theorem entry_39_2 (N : ℕ) :
    Filter.Tendsto (fun T : ℝ => ∫ x in (0 : ℝ)..T, Real.sin x ^ (N + 1) / x ^ (N + 1))
      Filter.atTop
      (nhds (Real.pi / (2 ^ (N + 1) * (N.factorial : ℝ)) *
        ∑ k ∈ Finset.range (N / 2 + 1),
          (∏ j ∈ Finset.range k, (-((N : ℝ) + 1) + (j : ℝ))) / (k.factorial : ℝ)
            * (((N : ℝ) + 1) - 2 * (k : ℝ)) ^ N)) := by sorry
end RamanujanNotebooks
