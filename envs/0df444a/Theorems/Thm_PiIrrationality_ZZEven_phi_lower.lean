-- Prove2me | Theorems.Thm_PiIrrationality_ZZEven_phi_lower
-- name    : PiIrrationality.ZZEven.phi_lower
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T09:46:47.333221+00:00
-- url     : https://prove2.me/theorems/89f94235-e35e-43c1-a3c1-2f0179bef4f8
-- title:
--   Prime saving: $\Phi_n\ge e^{(\lambda_K-\delta)n}$ from $K$ intervals of deleted primes
-- statement:
--   For every $K\ge0$ and every $\delta>0$, for all sufficiently large $n$,
--   $$
--   \Phi_n\ \ge\ \exp\Bigl(\bigl(\lambda_K-\delta\bigr)n\Bigr),\qquad
--   \lambda_K=\sum_{k=0}^{K-1}\Bigl(\frac{4}{2k+1}-\frac{6}{3k+2}\Bigr),
--   $$
--   where $\Phi_n$ is the product of Bai's deleted primes for the exponents $(2,4,6)$, as in the definition file `PiIrrationality_ZZEvenForms`.
--
--   For each $k$, every prime $p$ in the interval $\bigl(\tfrac{6n}{3k+2},\tfrac{4n}{2k+1}\bigr]$ that exceeds $\max(5,\sqrt{8n})$ is a deleted prime. Indeed $\{2n/p\}=\omega\in[\tfrac12,\tfrac23)$, and the defining inequality becomes $5\omega-\tfrac52<3\omega-1$. The prime number theorem gives these intervals a total logarithmic weight $\bigl(\tfrac{4}{2k+1}-\tfrac{6}{3k+2}\bigr)n+o(n)$. The values are $\lambda_1=1$, $\lambda_2=17/15$, $\lambda_3=17/15+1/20=71/60$, increasing to $2\bigl(\tfrac{\pi}{2\sqrt3}-\log\tfrac{3\sqrt3}{4}\bigr)=1.29055\ldots$, which is Zeilberger–Zudilin's (10) at index $2n$.
-- source:
--   D. Zeilberger and W. Zudilin, The irrationality measure of π is at most 7.103205334137…, Moscow J. Combin. Number Theory 9 (2020), no. 4, 407–419, arXiv:1912.06345, Lemma 3 and equation (10) (citing Hata, Lemma 2.2); Y. Bai, The irrationality measure of π is at most 7.101862832357, arXiv:2609.11276 (v2, 11 Sep 2026), Section 3 (removable-prime saving), with (a,b,c)=(2,4,6).

import Definitions.Def_PiIrrationality_ZZEvenForms
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Basic

theorem PiIrrationality.ZZEven.phi_lower (K : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp (((∑ k ∈ Finset.range K,
          ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2))) - δ) * (n : ℝ)) ≤
        (PiIrrationality.ZZEven.Phi n : ℝ) := by
  sorry
