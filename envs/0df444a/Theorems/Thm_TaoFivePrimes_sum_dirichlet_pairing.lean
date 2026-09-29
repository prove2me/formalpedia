-- Prove2me | Theorems.Thm_TaoFivePrimes_sum_dirichlet_pairing
-- name    : TaoFivePrimes.sum_dirichlet_pairing
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T19:33:55.433216+00:00
-- url     : https://prove2.me/theorems/d974fadb-d0c8-4129-80e1-141daf5f7960
-- title:
--   Pairing a Dirichlet convolution with a test function: $\sum_n (a*b)(n)F(n)=\sum_d a(d)\sum_m b(m)F(dm)$
-- statement:
--   Let $a,b$ be real-valued arithmetic functions, let $N$ be a natural number, and let $F:\mathbb N\to\mathbb C$ vanish at every $n\ge N$. Writing $*$ for Dirichlet convolution,
--
--   $$\sum_{n<N}(a*b)(n)\,F(n)\;=\;\sum_{d<N}\ \sum_{m<N}a(d)\,b(m)\,F(dm).$$
--
--   Pairing a Dirichlet convolution against a test function turns it into an iterated sum over the two factors. This is the mechanism by which each term of Vaughan's identity, which is an identity between arithmetic functions, becomes a bilinear sum in the divisor variables; it is the step that produces the Type I and Type II sums of Section 5 from Lemma 4.11.
--
--   **Formalization Note** Arithmetic functions are indexed from $0$ with value $0$ there, so the pairs with $d=0$ or $m=0$ contribute nothing; the pairs with $dm\ge N$ contribute nothing because $F$ vanishes from $N$ on. Both sums are therefore finite.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, Mathematics of Computation 83 (2014), 997-1038, https://arxiv.org/abs/1201.6656, Section 4, proof of Lemma 4.11, the step "We sum this against F ... to conclude that sum_n Lambda(n) F(n) = sum_{d <= U} mu(d) sum_n (log n) F(dn) - sum_{d <= UV} f(d) sum_n F(dn) + sum_{d > U} sum_{w > V} mu(d) (g(w) + (1/2) log w) F(dw)".

import Mathlib

theorem TaoFivePrimes.sum_dirichlet_pairing (a b : ArithmeticFunction ℝ) (F : ℕ → ℂ)
    (N : ℕ) (hF : ∀ n, N ≤ n → F n = 0) :
    ∑ n ∈ Finset.range N, (((a * b) n : ℝ) : ℂ) * F n
      = ∑ d ∈ Finset.range N, ∑ m ∈ Finset.range N,
          ((a d : ℝ) : ℂ) * ((b m : ℝ) : ℂ) * F (d * m) := by sorry
