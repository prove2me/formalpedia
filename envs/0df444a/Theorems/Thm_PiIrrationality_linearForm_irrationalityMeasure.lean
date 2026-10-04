-- Prove2me | Theorems.Thm_PiIrrationality_linearForm_irrationalityMeasure
-- name    : PiIrrationality.linearForm_irrationalityMeasure
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T01:47:49.269136+00:00
-- url     : https://prove2.me/theorems/5ac3309a-9ac4-43bf-84c4-ac0978325d99
-- title:
--   Hata–Zudilin linear-form bound for $\mu(\pi)$
-- statement:
--   Let $a_n$ and $b_n$ be rational integers, and let $C_0$, $C_1$, and $B$ be real numbers satisfying $C_0>0$, $C_1>0$, and
--   $$
--   1+\frac{C_1}{C_0}\le B.
--   $$
--   Set $\Lambda_n=b_n\pi-a_n$. Assume that the coefficient sequence obeys
--   $$
--   \limsup_{n\to\infty}\frac{\log|b_n|}{n}\le C_1,
--   $$
--   in the sense that for every $\varepsilon>0$ one has $b_n\neq 0$ and $\log|b_n|\le (C_1+\varepsilon)n$ for all sufficiently large $n$, and that the linear forms have a two-sided limit
--   $$
--   \lim_{n\to\infty}\frac{\log|\Lambda_n|}{n}=-C_0,
--   $$
--   again with $\Lambda_n\neq 0$ for every large $n$. Then
--   $$
--   \mu(\pi)\le B.
--   $$
--   Explicitly, for every $\varepsilon>0$ there is an integer $Q$ such that
--   $$
--   \left|\pi-\frac{p}{q}\right|>q^{-(B+\varepsilon)}
--   $$
--   whenever $p\in\mathbb{Z}$, $q$ is a positive integer, and $q\ge Q$.
--
--   The statement is the rational-integer case of the linear-form criterion for an irrationality measure. A sequence of integer forms $b_n\pi-a_n$ which decays exponentially, while $b_n$ grows at most exponentially, produces an explicit upper bound on $\mu(\pi)$. Zeilberger–Zudilin invoke this implication, through Salikhov’s Lemma 1, to pass from their normalized integrals $a_n'+b_n'\pi$ to the record $\mu(\pi)\le 7.103205334137\ldots$.
--
--   **Formalization Note.** The coefficients $a_n,b_n$ lie in $\mathbb{Z}$. The hypothesis on $\Lambda_n$ is the two-sided limit in Zudilin’s Proposition 1, not a limsup. The conclusion is `PiIrrationality.UpperBound B` for every real $B\ge 1+C_1/C_0$, which is the platform’s $\varepsilon$-form of $\mu(\pi)\le B$.
-- source:
--   W. Zudilin, An essay on irrationality measures of π and other logarithms, Chebyshevskii Sbornik 5 (2004), 49–65, arXiv:math/0404523, Proposition 1, citing M. Hata, Rational approximations to π and some other numbers, Acta Arith. 63 (1993), no. 4, 335–349, Lemma 3.1. The same implication is used by D. Zeilberger and W. Zudilin, The irrationality measure of π is at most 7.103205334137…, Moscow J. Combin. Number Theory 9 (2020), no. 4, 407–419, arXiv:1912.06345, section World record, via V. Kh. Salikhov, On the measure of irrationality of the number π, Math. Notes 88 (2010), no. 4, 563–573, Lemma 1.

import Definitions.Def_PiIrrationality_UpperBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter Real PiIrrationality

theorem PiIrrationality.linearForm_irrationalityMeasure
    (a b : ℕ → ℤ) (C0 C1 B : ℝ)
    (hC0 : 0 < C0) (hC1 : 0 < C1)
    (hB : 1 + C1 / C0 ≤ B)
    (hb : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      b n ≠ 0 ∧ Real.log |(b n : ℝ)| ≤ (C1 + ε) * n)
    (hΛ : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      0 < |(b n : ℝ) * Real.pi - (a n : ℝ)| ∧
        |Real.log |(b n : ℝ) * Real.pi - (a n : ℝ)| / (n : ℝ) + C0| ≤ ε) :
    UpperBound B := by sorry
