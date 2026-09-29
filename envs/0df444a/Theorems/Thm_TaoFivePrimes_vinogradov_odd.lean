-- Prove2me | Theorems.Thm_TaoFivePrimes_vinogradov_odd
-- name    : TaoFivePrimes.vinogradov_odd
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T23:54:54.064982+00:00
-- url     : https://prove2.me/theorems/e9ff8fbb-082d-46d9-a11b-0078a8b7acd4
-- title:
--   Tao Corollary 3.5: the Vinogradov-type lemma restricted to odd integers
-- statement:
--   Let $\alpha,\theta\in\mathbb R$ and $A,B>0$, and suppose $2\alpha=\frac aq+\beta$ for some integer $a$, some $q\ge1$ and some $\beta$ with $|\beta|\le1/q^{2}$. Then for all reals $x<y$,
--
--   $$\sum_{\substack{x<n\le y\\ n\ \text{odd}}}\min\!\left(A,\ \frac{B}{\bigl|\sin(\pi\alpha n+\theta)\bigr|}\right)
--   \;\le\;\left(\left\lfloor\frac{y-x}{2q}\right\rfloor+1\right)\left(2A+\frac{2}{\pi}\,Bq\log 4q\right),$$
--
--   the sum being over the odd integers of the interval $(x,y]$ and the term at a zero of the sine being read as $A$, in accordance with the convention $B/0=+\infty$.
--
--   This is the Vinogradov-type Lemma 3.4 with a factor of two saved in the block count, $\lfloor(y-x)/q\rfloor+1$ becoming $\lfloor(y-x)/(2q)\rfloor+1$, by restricting the summation to odd $n$. Together with the analogous saving in Corollary 3.2 it is what allows the exponential sums of Sections 5 and 6 to be summed over the odd integers only, which is where this paper improves on the classical treatment.
--
--   **Quoted input** Lemma 3.4 itself is attributed in the source to Davenport and Rademacher and is not available in the ambient library, so it appears here as a hypothesis, stated in the generality the deduction requires: for every frequency admitting a rational approximation with the same denominator $q$ and error at most $1/q^{2}$, every phase, and every interval.
--
--   **Formalization Note** The summand is written with an explicit case distinction at $\sin(\pi\alpha n+\theta)=0$, so that the value there is $A$; the ambient convention $B/0=0$ would otherwise make the term vanish and weaken both the hypothesis and the conclusion. The odd integers of $(x,y]$ are described by integer floor bounds.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 3, Corollary 3.5 (Restricting to odd integers)

import Mathlib

open Finset

theorem TaoFivePrimes.vinogradov_odd
    (A B : ℝ) (alpha beta theta : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (halpha : 2 * alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (x y : ℝ) (hxy : x < y)
    (hvino : ∀ (alpha' beta' theta' u v : ℝ) (a' : ℤ),
        alpha' = (a' : ℝ) / q + beta' → |beta'| ≤ 1 / (q : ℝ) ^ 2 → u < v →
        (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
            (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A
              else min A (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
          ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
              * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q))) :
    (∑ n ∈ (Finset.Ioc ⌊x⌋ ⌊y⌋).filter (fun n : ℤ => Odd n),
        (if Real.sin (Real.pi * alpha * (n : ℝ) + theta) = 0 then A
          else min A (B / |Real.sin (Real.pi * alpha * (n : ℝ) + theta)|)))
      ≤ ((⌊(y - x) / (2 * (q : ℝ))⌋ : ℤ) + 1)
          * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) := by sorry
