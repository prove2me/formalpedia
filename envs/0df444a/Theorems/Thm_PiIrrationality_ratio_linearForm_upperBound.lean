-- Prove2me | Theorems.Thm_PiIrrationality_ratio_linearForm_upperBound
-- name    : PiIrrationality.ratio_linearForm_upperBound
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T09:28:46.654195+00:00
-- url     : https://prove2.me/theorems/e178b375-19c9-4c1a-9fb3-6c5d9941c32f
-- title:
--   Index selection for integer linear forms in $1$ and $\pi$ (ratio form)
-- statement:
--   Let $U_n,V_n\in\mathbb{Z}$ and put $\Lambda_n=U_n+V_n\pi$. Let $s,t,g$ be real numbers with
--   $$
--   0<s,\qquad 0<t,\qquad s<g ,
--   $$
--   and assume that for all sufficiently large $n$:
--
--   1. $V_n\neq 0$ and $|V_n|\le e^{sn}$;
--   2. $|\Lambda_n|\le e^{-tn}$;
--   3. $|\Lambda_n|\le e^{-gn}\,|V_n|$.
--
--   Then every real $B$ with
--   $$
--   B\ \ge\ 1+\frac{s}{t}\qquad\text{and}\qquad B\ \ge\ 1+\frac{s}{g-s}
--   $$
--   is an upper bound for the irrationality measure of $\pi$. That is, for every $\varepsilon>0$ there is $Q$ such that $|\pi-p/q|>q^{-(B+\varepsilon)}$ for all integers $p$ and all integers $q\ge Q$.
--
--   This is Hata's index-selection argument, in the one-number form of Bai's Lemma 5.1. Bai assumes a two-sided limit $\frac1n\log|V_n|\to\sigma$. Here the lower bound on $|V_n|$ is replaced by hypothesis 3, which bounds the ratio $|\Lambda_n|/|V_n|$; for normalised forms $\Lambda_n=M_n\lambda_n$ this ratio does not depend on the normaliser. Only a limsup is needed for the decay of $\Lambda_n$, so the lemma applies to integrals whose dominant saddle points form a complex-conjugate pair, such as the Zeilberger–Zudilin integrals. With the exact rates $s=\sigma$, $t=\tau$ and $g=\sigma+\tau$, both conditions reduce to $B\ge 1+\sigma/\tau$.
-- source:
--   Y. Bai, The irrationality measure of π is at most 7.101862832357, arXiv:2609.11276 (v2, 11 Sep 2026), Section 5.1, Lemma 5.1 (Hata's index-selection lemma); M. Hata, Rational approximations to π and some other numbers, Acta Arith. 63 (1993), 335–349, Lemma 3.1.

import Definitions.Def_PiIrrationality_UpperBound
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

theorem PiIrrationality.ratio_linearForm_upperBound
    (U V : ℕ → ℤ) (s t g B : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hsg : s < g)
    (hB₁ : 1 + s / t ≤ B) (hB₂ : 1 + s / (g - s) ≤ B)
    (hV : ∀ᶠ n : ℕ in atTop, V n ≠ 0 ∧ |(V n : ℝ)| ≤ Real.exp (s * n))
    (hΛ : ∀ᶠ n : ℕ in atTop, |(U n : ℝ) + V n * Real.pi| ≤ Real.exp (-(t * n)))
    (hratio : ∀ᶠ n : ℕ in atTop,
      |(U n : ℝ) + V n * Real.pi| ≤ Real.exp (-(g * n)) * |(V n : ℝ)|) :
    PiIrrationality.UpperBound B := by
  sorry
