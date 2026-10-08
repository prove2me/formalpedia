-- Prove2me | Theorems.Thm_PiIrrationality_ZZEven_upperBound_of_saving
-- name    : PiIrrationality.ZZEven.upperBound_of_saving
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T09:28:58.479475+00:00
-- url     : https://prove2.me/theorems/9aa529c8-9f17-47d7-a892-a9b22f742599
-- title:
--   Irrationality-measure bound for $\pi$ from the even-index Zeilberger–Zudilin forms with $K$ prime intervals
-- statement:
--   Let $K\ge0$, $\delta>0$ and $B\in\mathbb{R}$. Put $\lambda_K=\sum_{k=0}^{K-1}\bigl(\frac{4}{2k+1}-\frac{6}{3k+2}\bigr)$ and
--   $$
--   s=25.22+10\delta-\log2-\lambda_K,\qquad t=5\log2-1-10\delta+\lambda_K,\qquad g-s=5\log2-1.02-11\delta+\lambda_K .
--   $$
--   If $s>0$, $g-s>0$,
--   $$
--   B\ \ge\ 1+\frac{s}{t}\qquad\text{and}\qquad B\ \ge\ 1+\frac{s}{g-s},
--   $$
--   then $B$ is an upper bound for the irrationality measure of $\pi$, in the sense of `PiIrrationality.UpperBound`.
--
--   This combines the explicit growth rates of the even-index Zeilberger–Zudilin forms $M_nJ_n=U_n+V_n\pi$:
--
--   1. $\operatorname{lcm}(1,\dots,8n)\le e^{8(1+\delta)n}$ (prime number theorem);
--   2. $\Phi_n\ge e^{(\lambda_K-\delta)n}$ (prime saving);
--   3. $\mathrm{coef}_n\le e^{17.22n}$ and $\mathrm{coef}_n\ge e^{17.20n}$;
--   4. $|J_n|\le 10e^{-7n}$.
--
--   These give $|V_n|\le e^{sn}$, $|M_nJ_n|\le e^{-tn}$ and $|M_nJ_n|\le e^{-gn}|V_n|$ with $g=24.2+4\log2-\delta$, and the index-selection lemma concludes. For $K=0,1,3$ and $\delta=10^{-3}$ the bound is about $11.08$, $7.85$ and $7.45$ respectively.
-- source:
--   Y. Bai, The irrationality measure of π is at most 7.101862832357, arXiv:2609.11276 (v2, 11 Sep 2026), Section 5.2 (application of Lemma 5.1 to the forms of Proposition 2.7), specialised to (a,b,c)=(2,4,6) with the explicit rates above; D. Zeilberger and W. Zudilin, The irrationality measure of π is at most 7.103205334137…, Moscow J. Combin. Number Theory 9 (2020), no. 4, 407–419, arXiv:1912.06345, World record paragraph.

import Definitions.Def_PiIrrationality_UpperBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem PiIrrationality.ZZEven.upperBound_of_saving (K : ℕ) (δ B : ℝ) (hδ : 0 < δ)
    (hs : 0 < 2522 / 100 + 10 * δ - Real.log 2 -
      ∑ k ∈ Finset.range K, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2)))
    (hgap : 0 < 5 * Real.log 2 - 102 / 100 - 11 * δ +
      ∑ k ∈ Finset.range K, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2)))
    (hB₁ : 1 + (2522 / 100 + 10 * δ - Real.log 2 -
        ∑ k ∈ Finset.range K, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2))) /
      (5 * Real.log 2 - 1 - 10 * δ +
        ∑ k ∈ Finset.range K, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2))) ≤ B)
    (hB₂ : 1 + (2522 / 100 + 10 * δ - Real.log 2 -
        ∑ k ∈ Finset.range K, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2))) /
      (5 * Real.log 2 - 102 / 100 - 11 * δ +
        ∑ k ∈ Finset.range K, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2))) ≤ B) :
    PiIrrationality.UpperBound B := by
  sorry
