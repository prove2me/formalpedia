-- Prove2me | Theorems.Thm_TaoFivePrimes_vaughan_decomposition
-- name    : TaoFivePrimes.vaughan_decomposition
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T19:33:58.469369+00:00
-- url     : https://prove2.me/theorems/2dc9b1b2-34ef-4cc3-a67a-ceb2e7c0b5d5
-- title:
--   Tao Lemma 4.11: the Type I / Type II decomposition of a smoothed prime sum
-- statement:
--   Let $U,V>0$, let $N$ be a positive integer, and let $F$ be a complex-valued function on the positive integers that vanishes at every $n\ge N$ and at every $n\le V$. Write $\mu$ for the Möbius function, $\Lambda$ for the von Mangoldt function, $1$ for the constant-one arithmetic function, and, for an arithmetic function $f$, write $f_{\le U}$ and $f_{>U}$ for its restrictions to arguments at most $U$ and greater than $U$. Then
--
--   $$\sum_{n<N}\Lambda(n)F(n)
--   \;=\;\sum_{d,m}\mu_{\le U}(d)\,\log(m)\,F(dm)
--   \;-\;\sum_{d,m}\bigl(\mu_{\le U}*\Lambda_{\le V}\bigr)(d)\,F(dm)
--   \;+\;\sum_{d,w}\mu_{>U}(d)\,\bigl(\Lambda_{>V}*1\bigr)(w)\,F(dw),$$
--
--   all sums over $d,m,w<N$, and $*$ denoting Dirichlet convolution.
--
--   This is the variant of Vaughan's identity on which Section 5 rests: the first two terms are Type I sums, in which one variable runs over a short range and the other carries a smooth weight, while the third is the Type II bilinear sum handled by the large sieve. The hypothesis that $F$ vanishes on $[0,V]$ is what removes the diagonal term of the classical identity.
--
--   **Formalization Note** Arithmetic functions are indexed from $0$, with the value at $0$ equal to $0$; the truncations and the Dirichlet convolution are those of the ambient library, and the sums are finite because $F$ vanishes from $N$ on.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 4, Lemma 4.11 (A variant of Vaughan's identity), equation (4.18)

import Mathlib
import Definitions.Def_TaoFivePrimes_VaughanTruncation

theorem TaoFivePrimes.vaughan_decomposition (U V : ℝ) (F : ℕ → ℂ) (N : ℕ)
    (hFN : ∀ n, N ≤ n → F n = 0)
    (hFV : ∀ n : ℕ, (n : ℝ) ≤ V → F n = 0) :
    ∑ n ∈ Finset.range N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * F n
      = (∑ d ∈ Finset.range N, ∑ m ∈ Finset.range N,
            ((TaoFivePrimes.truncLe U TaoFivePrimes.moebiusR d : ℝ) : ℂ) *
              ((ArithmeticFunction.log m : ℝ) : ℂ) * F (d * m))
        - (∑ d ∈ Finset.range N, ∑ m ∈ Finset.range N,
            (((TaoFivePrimes.truncLe U TaoFivePrimes.moebiusR *
                TaoFivePrimes.truncLe V ArithmeticFunction.vonMangoldt) d : ℝ) : ℂ) *
              ((TaoFivePrimes.zetaR m : ℝ) : ℂ) * F (d * m))
        + (∑ d ∈ Finset.range N, ∑ w ∈ Finset.range N,
            ((TaoFivePrimes.truncGt U TaoFivePrimes.moebiusR d : ℝ) : ℂ) *
              (((TaoFivePrimes.truncGt V ArithmeticFunction.vonMangoldt *
                  TaoFivePrimes.zetaR) w : ℝ) : ℂ) * F (d * w)) := by sorry
