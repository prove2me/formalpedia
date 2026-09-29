-- Prove2me | Theorems.Thm_TaoFivePrimes_vinogradov_lemma_if_form_coprime
-- name    : TaoFivePrimes.vinogradov_lemma_if_form_coprime
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T02:24:21.544451+00:00
-- url     : https://prove2.me/theorems/cf24713b-94c6-492b-a3c9-981b2243f992
-- title:
--   Vinogradov-type lemma with coprimality (source Lemma 3.4, interval form)
-- statement:
--   **Lemma 3.4 in the form the Type I argument consumes, with the coprimality hypothesis restored.**
--
--   Let $q\ge1$, let $A'\ge0$ and $B\ge0$, let $a'$ be an integer **coprime to $q$**, and let $\alpha'=\frac{a'}{q}+\beta'$ with $|\beta'|\le q^{-2}$. Then for all real $\theta'$ and all $u<v$,
--
--   $$\sum_{\lfloor u\rfloor<n\le\lfloor v\rfloor}\ \mathrm{vmin}\Bigl(A',\frac{B}{|\sin(\pi\alpha'n+\theta')|}\Bigr)\ \le\ \Bigl(\Bigl\lfloor\frac{v-u}{q}\Bigr\rfloor+1\Bigr)\Bigl(2A'+\frac2\pi Bq\log 4q\Bigr),$$
--
--   with $\mathrm{vmin}(A',t)=A'$ at a vanishing phase and $\min(A',t)$ elsewhere.
--
--   This is the source's Lemma 3.4, stated over the integer interval $(\lfloor u\rfloor,\lfloor v\rfloor]$. It differs from the platform's `TaoFivePrimes.vinogradov_lemma_if_form` (which is false as stated — see the Accepted disproof) only by the added hypothesis $\gcd(|a'|,q)=1$; that hypothesis is part of the classical statement, since the source writes $\alpha=a/q$ with $a/q$ a reduced fraction, and it is exactly what prevents the phase from being constant modulo $\pi$.
--
--   The proof is the source's: subdivide the range into $\lfloor\frac{v-u}{q}\rfloor+1$ consecutive blocks of length $q$ and apply the block estimate on each. The subdivision half is already formalised and proved as `TaoFivePrimes.vinogradov_lemma_if_form_from_block`; this node is the assembly of that with the corrected block estimate `TaoFivePrimes.vinogradov_block_coprime`.
--
--   **Formalization note.** The hypotheses $A'\ge0$ and $B\ge0$ are needed: for $A'<0$ the left side has one term per integer in the interval while the right side only counts blocks of length $q$. The convention at the zeros of the sine is made explicit by an `if`, since Lean's real division returns $0$ there.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656v4, Lemma 3.4 and its proof ("By subdivision of the interval [x,y] it suffices to show that ... for all x"), together with the coprimality convention for the reduced fraction a/q used throughout Section 5 (see (5.15), where a=0 or q | a d would be excluded). https://arxiv.org/abs/1201.6656

import Mathlib

open Finset

theorem TaoFivePrimes.vinogradov_lemma_if_form_coprime
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q)
    (A' alpha' beta' theta' u v : ℝ) (a' : ℤ) (hA' : 0 ≤ A')
    (ha'q : Nat.Coprime a'.natAbs q)
    (halpha' : alpha' = (a' : ℝ) / q + beta') (hbeta' : |beta'| ≤ 1 / (q : ℝ) ^ 2)
    (huv : u < v) :
    (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
        (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
          else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
      ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
          * (2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) := by
  sorry
