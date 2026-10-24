-- Prove2me | Theorems.Thm_RecMarkovGraph_IndepLB_lemma_4_3
-- name    : RecMarkovGraph.IndepLB.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:37.604753+00:00
-- url     : https://prove2.me/theorems/cc793cde-ab90-4d4e-af3f-f54ebeea4cee
-- title:
--   Lemma 4.3, p. 10 (corrected: f_1 := f_1(a x_1)) — for n ≥ (1/f_1 − 1)², a x_1 + η + 2/(1+√n) + log n ≤ a Σ_{i≤n} x_i ≤ a x_1 + log(1 + (n−1)x_1)
-- statement:
--   Let $a\in(0,1]$, $x_1\in(0,1)$ and $x_{n+1}=x_n(1-ax_n)$. Put $f_1:=f_1(ax_1)=ax_1(1-ax_1)$ and
--   $$\eta:=2(1-f_1)\log f_1-\Bigl(\tfrac52+\log2\Bigr)f_1 .$$
--   Then for every $n$ with $n\ge(1/f_1-1)^2$,
--   $$a x_1+\eta+\frac{2}{1+\sqrt n}+\log n\ \le\ a\sum_{i=1}^n x_i\ \le\ a x_1+\log\bigl(1+(n-1)x_1\bigr).$$
--
--   The partial sums of the recursion therefore grow like $\frac1a\log n$; applied with $a=\gamma$ this gives the expected row sums $\mathbb E S_n\sim\log n/\gamma$ behind Corollary 4.6 and Theorem 2.2.
--
--   Differences from the source:
--   - correction: f_1 := f_1(x_1), in η(x_1) and in the threshold n ⩾ (1/f_1 − 1)^2 → f₁ := fa 1 (a * x₁), i.e. f_1(a x_1), in η and in the threshold; reason: the printed lower bound is false for a < 1: a = 0.05, x_1 = 0.1, n = 1000 gives left side 2.304 > a Σ x_i = 1.791; the proof scales by y_n = a x_n, which yields f_1(a x_1); the upper bound is kept as printed
--   - encoding: Σ_{i=1}^n x_i; √n; log → ∑ i ∈ range n, recSeq a x₁ i; Real.sqrt of (n : ℝ); Real.log; reason: 0-based sequence index; same numbers
-- source:
--   Gupte, Zhu, Large independent sets in recursive Markov random graphs, arXiv:2207.04514v4, p. 10, Lemma 4.3 (proof in §9, pp. 23–25)

import Mathlib
import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

open Finset

theorem lemma_4_3 (a x₁ : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hx₁ : 0 < x₁) (hx₁1 : x₁ < 1) :
    let f₁ := fa 1 (a * x₁)
    let η := 2 * (1 - f₁) * Real.log f₁ - (5 / 2 + Real.log 2) * f₁
    ∀ n : ℕ, (1 / f₁ - 1) ^ 2 ≤ (n : ℝ) →
      a * x₁ + η + 2 / (1 + Real.sqrt n) + Real.log n ≤ a * ∑ i ∈ range n, recSeq a x₁ i ∧
      a * ∑ i ∈ range n, recSeq a x₁ i ≤ a * x₁ + Real.log (1 + ((n : ℝ) - 1) * x₁) := by sorry

end RecMarkovGraph.IndepLB
