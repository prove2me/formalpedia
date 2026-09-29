-- Prove2me | Theorems.Thm_TaoFivePrimes_vinogradov_lemma
-- name    : TaoFivePrimes.vinogradov_lemma
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T01:37:46.699916+00:00
-- url     : https://prove2.me/theorems/97dda814-1fb8-4365-ab63-c4ac7e9ff4a0
-- title:
--   Tao Lemma 3.4: the Vinogradov-type lemma for sums of reciprocal-sine weights
-- statement:
--   Let $\alpha=\frac aq+\beta$ with $\beta=\mathcal O^*(1/q^2)$. Then for any $x<y$, any $A,B>0$ and any phase $\theta$,
--
--   $$\sum_{x<n\le y}\min\!\left(A,\frac{B}{|\sin(\pi\alpha n+\theta)|}\right)\;\le\;\left(\left\lfloor\frac{y-x}{q}\right\rfloor+1\right)\left(2A+\frac{2}{\pi}Bq\log 4q\right).$$
--
--   Here $a$ is an integer, $q$ a positive integer, and the notation $\beta=\mathcal O^*(1/q^2)$ means $|\beta|\le q^{-2}$; the sum runs over the integers of the half-open interval $(x,y]$.
--
--   This is the Vinogradov-type lemma that converts a rational approximation $a/q$ to $\alpha$ into a bound for a sum of the reciprocal-sine weights that arise when Lemma 3.1 is applied term by term along an interval. It is the tool that lets a bound of the shape $\min(A,B/|\sin|)$, obtained frequency by frequency, be summed over a whole range of $n$ at a total cost proportional to the number $\lfloor (y-x)/q\rfloor+1$ of length-$q$ blocks the range meets; it is what turns the pointwise estimates of Section 3 into the Type I sums of Section 5, and it is the input to the odd-restricted Corollary 3.5.
--
--   **Quoted input** The estimate for a single block of $q$ consecutive integers,
--   $$\sum_{m<n\le m+q}\min\!\left(A,\frac{1}{|\sin(\pi\alpha n+\theta)|}\right)\le 2A+\frac{2}{\pi}q\log 4q,$$
--   is quoted by the source from Deshouillers–Effinger–te Riele–Zinoviev, and appears here as a hypothesis; the content formalized is the source's own reduction of the general interval to that case, together with the normalization in $B$. The source notes that the cited lemma is stated without the phase shift $\theta$, but that its proof is unchanged in the presence of one.
--
--   **Formalization Note** The interval endpoints are real and the interval is half-open, so its integers are $\lfloor x\rfloor<n\le\lfloor y\rfloor$. The phase is carried as a real number rather than an element of $\mathbb R/\mathbb Z$, which is harmless because $|\sin|$ has period $\pi$. Where $\sin(\pi\alpha n+\theta)=0$ the quotient $B/|\sin(\pi\alpha n+\theta)|$ evaluates to $0$ under the ambient division convention rather than to $+\infty$; since the assertion is an upper bound for the sum, this only weakens the left-hand side and the statement remains a faithful consequence of the source's.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 3, Lemma 3.4 (Vinogradov-type lemma); the quoted single-block estimate is cited there to J.-M. Deshouillers, G. Effinger, H. te Riele, D. Zinoviev, A complete Vinogradov 3-primes theorem under the Riemann hypothesis, Electron. Res. Announc. Amer. Math. Soc. 3 (1997), 99-104, Lemma 1

import Mathlib

open Finset

theorem TaoFivePrimes.vinogradov_lemma (alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (halpha : alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (theta x y : ℝ) (hxy : x < y)
    (hblock : ∀ (A' theta' : ℝ), 0 < A' → ∀ m : ℤ,
      (∑ n ∈ Finset.Ioc m (m + (q : ℤ)),
          min A' (1 / |Real.sin (Real.pi * (alpha * (n : ℝ)) + theta')|))
        ≤ 2 * A' + (2 / Real.pi) * (q : ℝ) * Real.log (4 * q)) :
    (∑ n ∈ Finset.Ioc ⌊x⌋ ⌊y⌋,
        min A (B / |Real.sin (Real.pi * (alpha * (n : ℝ)) + theta)|))
      ≤ ((⌊(y - x) / (q : ℝ)⌋ : ℝ) + 1)
          * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) := by sorry
