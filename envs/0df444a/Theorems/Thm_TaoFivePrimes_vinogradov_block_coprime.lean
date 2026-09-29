-- Prove2me | Theorems.Thm_TaoFivePrimes_vinogradov_block_coprime
-- name    : TaoFivePrimes.vinogradov_block_coprime
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T02:24:19.19083+00:00
-- url     : https://prove2.me/theorems/32cd79af-0713-4cdc-893a-e83c32a12a18
-- title:
--   Vinogradov block estimate with coprimality (source Lemma 3.4, block form)
-- statement:
--   **The single-block Vinogradov estimate, with the coprimality hypothesis restored.**
--
--   Let $q\ge1$, let $A'\ge0$ and $B\ge0$, let $a'$ be an integer **coprime to $q$**, and let $\alpha'=\frac{a'}{q}+\beta'$ with $|\beta'|\le q^{-2}$. Then for every real $\theta'$ and every integer $m$,
--
--   $$\sum_{m<n\le m+q}\ \mathrm{vmin}\Bigl(A',\frac{B}{|\sin(\pi\alpha'n+\theta')|}\Bigr)\ \le\ 2A'+\frac2\pi Bq\log 4q,$$
--
--   where $\mathrm{vmin}(A',t)$ denotes $A'$ when the sine vanishes and $\min(A',t)$ otherwise.
--
--   This is the inequality to which the source's Lemma 3.4 reduces by subdivision: Tao's proof says "by subdivision of the interval $[x,y]$ it suffices to show that $\sum_{x<n\le x+q}\min(A,\frac1{|\sin(\pi\alpha n+\theta)|})\le 2A+\frac2\pi q\log 4q$ for all $x$; the claim then follows from [8, Lemma 1]". It is the block estimate, not the subdivided one, that carries the analytic content, and it is stated here on its own so that the subdivision step (a purely combinatorial covering argument, already formalised as `TaoFivePrimes.vinogradov_lemma_if_form_from_block`) is separated from it.
--
--   **Why the coprimality hypothesis is needed.** The platform's `TaoFivePrimes.vinogradov_block_if_form` was **Disproved**, and `TaoFivePrimes.vinogradov_lemma_if_form` is false, for the same reason: without $\gcd(|a'|,q)=1$ the phase can be constant modulo $\pi$. For $a'=0$, $\beta'=\theta'=0$ one has $\sin(\pi\alpha'n+\theta')=0$ for every $n$, so each of the $q$ terms of a block contributes $A'$ while the right-hand side pays only $2A'$. With $\gcd(|a'|,q)=1$ the residues $a'n\bmod q$ run through all of $\mathbb Z/q\mathbb Z$ as $n$ runs over any $q$ consecutive integers, so the phase can vanish for at most one $n$ in the block; that single term is what the $2A'$ slot pays for.
--
--   **Formalization note.** The summand is written with an explicit `if` at the zeros of the sine rather than as a bare `min`: in Lean's real division $B/0$ is $0$, so `min A' (B/|sin|)` would silently contribute $0$ at a vanishing phase, whereas the source's convention (and the mathematically correct value of the minimum there) is $A'$. The block is the integer interval $(m,m+q]$, matching the shape that the subdivision lemma consumes. The variables $A',B,q$ are fixed first so that the statement can be used uniformly inside an induction over blocks.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656v4, Lemma 3.4 and its proof ("By subdivision of the interval [x,y] it suffices to show that ... for all x"), together with the coprimality convention for the reduced fraction a/q used throughout Section 5 (see (5.15), where a=0 or q | a d would be excluded). https://arxiv.org/abs/1201.6656

import Mathlib

open Finset

theorem TaoFivePrimes.vinogradov_block_coprime
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q)
    (A' alpha' beta' theta' : ℝ) (a' : ℤ) (hA' : 0 ≤ A')
    (ha'q : Nat.Coprime a'.natAbs q)
    (halpha' : alpha' = (a' : ℝ) / q + beta') (hbeta' : |beta'| ≤ 1 / (q : ℝ) ^ 2)
    (m : ℤ) :
    (∑ n ∈ Finset.Ioc m (m + (q : ℤ)),
        (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
          else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
      ≤ 2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) := by
  sorry
