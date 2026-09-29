-- Prove2me | Theorems.Thm_TaoFivePrimes_typeII_counting_bounds
-- name    : TaoFivePrimes.typeII_counting_bounds
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T04:59:17.902981+00:00
-- url     : https://prove2.me/theorems/3f7bd353-18f4-4e63-b083-4f27224a8cb2
-- title:
--   Tao Section 5: the two counting bounds of the Type II estimate
-- statement:
--   Let $x>0$ and $W\ge2$. Let $S$ be a finite set of odd integers contained in $[\frac{x}{2W},\frac xW]$ and $T$ a finite set of odd integers contained in $[\frac W2,W]$. Then
--
--   $$|S|\ \le\ \frac{x}{4W}+1,\qquad \sum_{w\in T}\log^2 w\ \le\ \Bigl(\frac W4+1\Bigr)\log^2 W.$$
--
--   These are the two counting bounds
--   $$A=\sum_{d\in[\frac x{2W},\frac xW]}\mathbf 1_{(d,2)=1},\qquad B=\sum_{w\in[\frac W2,W]}\mathbf 1_{(w,2)=1}\log^2w$$
--   that enter the source's Type II estimate after the bilinear sum has been split dyadically and the large sieve applied: $A$ and $B$ are the $\ell^2$ masses of the two coefficient sequences, and the estimate proceeds by bounding $A^{1/2}B^{1/2}$. Both come from the same elementary fact, that a set of odd integers inside a real interval of length $L$ has at most $\frac L2+1$ elements, applied to intervals of lengths $\frac x{2W}$ and $\frac W2$; for $B$ one first replaces $\log^2w$ by $\log^2W$, legitimate because $1\le w\le W$ on the range.
--
--   **Formalization Note** The two ranges are given as hypotheses on arbitrary finite sets of odd integers rather than as explicit `Finset`s, which is how they are used and which avoids committing to a particular description of the integers of a real interval. The hypothesis $W\ge2$ is what makes $w\ge W/2\ge1$, so that $\log w\ge0$ and squaring preserves the inequality $\log w\le\log W$.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5 (Minor arcs), subsection "Estimation of the Type II sum", the displays "|A| <= x/(4W) + 1" and "|B| <= (W/4 + 1) log^2 W" following the definitions of A and B after equation (del1)

import Mathlib

open Finset

theorem TaoFivePrimes.typeII_counting_bounds (x W : ℝ) (hx : 0 < x) (hW : 2 ≤ W)
    (S T : Finset ℤ)
    (hS : ∀ n ∈ S, Odd n) (hSm : ∀ n ∈ S, x / (2 * W) ≤ (n : ℝ) ∧ (n : ℝ) ≤ x / W)
    (hT : ∀ n ∈ T, Odd n) (hTm : ∀ n ∈ T, W / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ W) :
    (S.card : ℝ) ≤ x / (4 * W) + 1
      ∧ (∑ n ∈ T, Real.log (n : ℝ) ^ 2) ≤ (W / 4 + 1) * Real.log W ^ 2 := by sorry
