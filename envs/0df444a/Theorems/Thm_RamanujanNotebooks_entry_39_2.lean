-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_39_2
-- name    : RamanujanNotebooks.entry_39_2
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T08:29:12.459825+00:00
-- url     : https://prove2.me/theorems/da9804fc-f96a-41ee-b562-0e2862455ca5
-- title:
--   Integral over the positive axis of the n-th power of sin x / x, as a finite alternating sum
-- statement:
--   Entry 2 of Chapter 39, p. 566. For every positive integer n, the integrals ∫_0^T (sin x / x)^n dx tend, as T → ∞, to π/(2^n (n−1)!) · ∑_{k=0}^{⌊(n−1)/2⌋} ((−n)_k / k!) (n − 2k)^{n−1}, where (−n)_k = (−n)(−n+1)⋯(−n+k−1), so that (−n)_k/k! = (−1)^k C(n,k). Differs from the printed source: The finite sum in the print lacks $1/k!$. Here $(-n)_k/k!=(-1)^k C(n,k)$. At $n=5$, the printed expression gives $5\pi/16$ and the integral gives $115\pi/384$. The printed sign equals $1$ for either parity. Proper-integral limits also cover the conditionally convergent case $n=1$.
--
--   **Discrepancy from the printed source.** The finite sum in the print lacks $1/k!$. Here $(-n)_k/k!=(-1)^k C(n,k)$. At $n=5$, the printed expression gives $5\pi/16$ and the integral gives $115\pi/384$. The printed sign equals $1$ for either parity. Proper-integral limits also cover the conditionally convergent case $n=1$.
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
