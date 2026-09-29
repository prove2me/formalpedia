-- Prove2me | Theorems.Thm_TaoFivePrimes_vinogradov_block_if_form
-- name    : TaoFivePrimes.vinogradov_block_if_form
-- status  : Disproved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T18:46:51.420252+00:00
-- url     : https://prove2.me/theorems/00db332f-5aa3-4dd1-9131-cd55f357217c
-- title:
--   Tao Lemma 3.4: the Dress-Ramare block estimate
-- statement:
--   **The single-block estimate behind the Vinogradov-type lemma.** Let $\alpha'=\frac{a'}{q}+\beta'$ with $|\beta'|\le q^{-2}$ and $q\ge1$, let $A',B\ge0$ and $\theta'\in\mathbb R$. Then for every integer $m$,
--
--   $$\sum_{m<n\le m+q}\min\Bigl(A',\frac{B}{|\sin(\pi\alpha'n+\theta')|}\Bigr)\ \le\ 2A'+\frac2\pi Bq\log4q,$$
--
--   a term whose sine vanishes contributing $A'$.
--
--   This is the block estimate the source quotes from Dress and Ramaré as the engine of its Lemma 3.4: over $q$ consecutive integers the points $\alpha'n+\frac{\theta'}\pi$ are, up to the error $\beta'$, spread over the residues mod $q$, so at most two of them come within $\frac1{2q}$ of an integer and the rest are handled by the harmonic sum $\sum_{1\le k\le q/2}\frac{1}{\sin(\pi k/q)}$. The source notes that the phase shift $\theta'$, absent from the quoted statement, does not affect the argument.
--
--   **Formalization Note** $A'\ge0$ is needed: with $A'<0$ every term equals $A'$ and the left side has $q$ of them against $2A'$ on the right. The convention at the zeros of the sine is made explicit through the `if`, so that the statement is the one the Type I estimate of Section 5 consumes; in Lean the literal `min A' (B / 0)` would be $0$ rather than $A'$.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 3, Lemma 3.4 (Vinogradov-type lemma), the block estimate quoted from F. Dress, O. Ramare (and R. Baker), with the phase shift and the convention at the zeros of the sine

import Mathlib

open Finset

theorem TaoFivePrimes.vinogradov_block_if_form
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q)
    (A' alpha' beta' theta' : ℝ) (a' : ℤ) (hA' : 0 ≤ A')
    (halpha' : alpha' = (a' : ℝ) / q + beta') (hbeta' : |beta'| ≤ 1 / (q : ℝ) ^ 2)
    (m : ℤ) :
    (∑ n ∈ Finset.Ioc m (m + (q : ℤ)),
        (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
          else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
      ≤ 2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) := by sorry
