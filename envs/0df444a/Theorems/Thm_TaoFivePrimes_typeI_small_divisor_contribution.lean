-- Prove2me | Theorems.Thm_TaoFivePrimes_typeI_small_divisor_contribution
-- name    : TaoFivePrimes.typeI_small_divisor_contribution
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T04:31:10.8622+00:00
-- url     : https://prove2.me/theorems/feabfd7f-bf15-447f-ab2c-f79a3c79c9ad
-- title:
--   Tao Section 5: the divisors $d \le q/2$ contribute $A + \tfrac1\pi Bq\log 4q$ to the Type I envelope
-- statement:
--   Let $q\ge2$, let $a$ be an integer, let $\alpha,\beta$ satisfy $4\alpha=\frac aq+\beta$ with $|\beta|\le q^{-2}$, and let $A,B\ge0$. Then
--
--   $$\sum_{\substack{1\le d\le q/2\\ d\ \mathrm{odd}}}\min\!\left(A,\frac{B}{|\sin(2\pi d\alpha)|}\right)\ \le\ A+\frac{1}{\pi}Bq\log 4q,$$
--
--   with the convention that the summand equals $A$ where the sine vanishes.
--
--   This is the contribution of the small divisors $d\le q/2$ to the Type I envelope in the source's minor-arc theorem. The point is the factor of two: applying the odd-restricted Vinogradov-type lemma directly to $(0,q/2]$ would give $2A+\frac2\pi Bq\log4q$, but the weight is even in $d$, so the same application to a symmetric range of length $q+1$ — still short enough for the lemma's block count to be $1$ — bounds *twice* the sum above by that same quantity.
--
--   **Quoted input** The Vinogradov-type lemma of the source (its Lemma 3.4, for the modulus $q$ and the fixed truncation parameters $A,B$) appears here as the hypothesis `hvino`; the odd-restricted form actually used is the source's Corollary 3.5, which is public and proved and is applied to it.
--
--   **Formalization Note** The divisor range is written as the odd integers of $(0,\lfloor q/2\rfloor]$. The frequency is written $\pi\cdot(2\alpha)\cdot d$ rather than $2\pi d\alpha$ so as to match the shape in which Corollary 3.5 consumes it. At the zeros of the sine the summand is set to $A$, which is the source's convention and the mathematically correct value of the minimum there; the ambient division convention would instead make the quotient $0$.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5 (Minor arcs), subsection "Estimation of the Type I sum", the two displays following equation (daa) ("By Corollary 3.5 one has ... so by symmetry we may thus bound the contribution of the d <= q/2 terms")

import Mathlib

open Finset

theorem TaoFivePrimes.typeI_small_divisor_contribution
    (A B alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 2 ≤ q)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (halpha : 4 * alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hvino : ∀ (alpha' beta' theta' u v : ℝ) (a' : ℤ),
        alpha' = (a' : ℝ) / q + beta' → |beta'| ≤ 1 / (q : ℝ) ^ 2 → u < v →
        (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
            (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A
              else min A (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
          ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
              * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q))) :
    (∑ d ∈ (Finset.Ioc (0 : ℤ) ⌊(q : ℝ) / 2⌋).filter (fun d : ℤ => Odd d),
        (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then A
          else min A (B / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|)))
      ≤ A + (1 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) := by sorry
