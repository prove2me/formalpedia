-- Prove2me | Theorems.Thm_PiIrrationality_Bai_phi_lower_lam_of_MediumPNT
-- name    : PiIrrationality.Bai.phi_lower_lam_of_MediumPNT
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T19:57:33.314983+00:00
-- url     : https://prove2.me/theorems/55126396-27c4-4ad5-88bb-1f6683f3eecc
-- title:
--   Prime saving $\Phi_n\ge e^{(\lambda_K(L)-\delta)n}$ for any admissible interval table, from MediumPNT
-- statement:
--   Assume the MediumPNT statement $\psi(x)-x=O\big(x\,e^{-c(\log x)^{1/10}}\big)$ for some $c>0$. Let $L$ be a list of admissible rows (`okRow`) that is ordered (`chainOk`). Then for every $K$ and every $\delta>0$, for all large $n$,
--   $$\Phi_n\ge\exp\big((\lambda_K(L)-\delta)\,n\big),\qquad \lambda_K(L)=\sum_{m<K}\sum_k\Big(\frac{1}{m+A_k/D}-\frac{1}{m+B_k/D}\Big).$$
--
--   Role: the analytic half of Bai's prime saving (Section 3); the deleted primes (2.14) in $M_n$ contribute $\lambda_K(L)$ per $n$.
-- source:
--   Y. Bai, The irrationality measure of π is at most 7.101862832357, arXiv:2609.11276 (v2, 11 Sep 2026), https://arxiv.org/abs/2609.11276, (2.14), (3.1) and Section 3 (prime saving omega)

import Definitions.Def_PiIrrationality_BaiForms
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter

theorem PiIrrationality.Bai.phi_lower_lam_of_MediumPNT
    (L : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (hL : L.all PiIrrationality.Bai.okRow = true)
    (hc : PiIrrationality.Bai.chainOk L = true)
    (hPNT : ∃ c > 0, (Chebyshev.psi - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
    (K : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp ((PiIrrationality.Bai.lam L K - δ) * (n : ℝ)) ≤ (PiIrrationality.Bai.Phi n : ℝ) := by
  sorry
