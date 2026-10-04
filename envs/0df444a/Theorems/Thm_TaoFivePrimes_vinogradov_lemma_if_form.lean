-- Prove2me | Theorems.Thm_TaoFivePrimes_vinogradov_lemma_if_form
-- name    : TaoFivePrimes.vinogradov_lemma_if_form
-- status  : Disproved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T18:33:42.836103+00:00
-- url     : https://prove2.me/theorems/15c69f72-4cf0-4d42-ba38-73347a6f97bd
-- title:
--   Tao Lemma 3.4 in the form the Type I estimate consumes
-- statement:
--   **The Vinogradov-type lemma in the form the Type I argument consumes.** Let $\alpha'=\frac{a'}{q}+\beta'$ with $|\beta'|\le q^{-2}$ and $q\ge1$, let $A'\ge0$ and $B\ge0$, let $\theta'\in\mathbb R$ and $u<v$. Then
--
--   $$\sum_{\lfloor u\rfloor<n\le\lfloor v\rfloor}\min\Bigl(A',\frac{B}{|\sin(\pi\alpha'n+\theta')|}\Bigr)\ \le\ \Bigl(\Bigl\lfloor\frac{v-u}{q}\Bigr\rfloor+1\Bigr)\Bigl(2A'+\frac2\pi Bq\log4q\Bigr),$$
--
--   with the convention that a term whose sine vanishes contributes $A'$.
--
--   This is the source's Lemma 3.4, stated over the integer interval $(\lfloor u\rfloor,\lfloor v\rfloor]$ and with the convention at the zeros of the sine made explicit, so that it can be used as a hypothesis by the Type I estimate of Section 5. The proof is the source's: normalise $B=1$, subdivide $[u,v]$ into at most $\lfloor\frac{v-u}{q}\rfloor+1$ intervals of length $q$, and apply the block estimate of Dress–Ramaré on each — the phase shift $\theta'$ does not affect that argument.
--
--   **Formalization Note** The hypotheses $A'\ge0$ and $B\ge0$ are needed: for $A'<0$ the inequality can fail, since the left side then has one term per integer in the interval while the right side counts blocks of length $q$. The platform's `TaoFivePrimes.vinogradov_lemma` is the same statement in `min` form with the Dress–Ramaré block estimate carried as an explicit hypothesis; this version absorbs it and fixes the convention at the sine's zeros.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 3, Lemma 3.4 (Vinogradov-type lemma), over the integer interval and with the convention at the zeros of the sine

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums

open Finset

theorem TaoFivePrimes.vinogradov_lemma_if_form (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q)
    (A' alpha' beta' theta' u v : ℝ) (a' : ℤ) (hA' : 0 ≤ A')
    (halpha' : alpha' = (a' : ℝ) / q + beta') (hbeta' : |beta'| ≤ 1 / (q : ℝ) ^ 2)
    (huv : u < v) :
    (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
        (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
          else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
      ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
          * (2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) := by sorry
