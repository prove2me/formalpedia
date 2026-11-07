-- Prove2me | Theorems.Thm_SelfSelReg_lemma_5_7
-- name    : SelfSelReg.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:25.741199+00:00
-- url     : https://prove2.me/theorems/4fff4dec-246c-4f8b-9fb2-6ca50b823b92
-- title:
--   Lemma 5.7 — positivity and ratio bounds of the restricted moment coefficients $a_d(\sigma^2)$
-- statement:
--   Let $B\ge1$, $\Delta\in(0,1]$ and $K=16(1+B^2)^3/\Delta^4$. Let $s\ge1$ be an integer and $T>0$ with $T^2\ge Ks$. For every $\sigma^2\in[1+\Delta^2,1+B^2]$ the coefficients $a_d(\sigma^2)=\int_T^{T+1}\phi_{\sigma^2}(t)\mathrm{He}_d(t/\sigma)/(\sigma^d\sqrt{d!})\,dt$ are positive for $0\le d\le 2s+2$, and for every pair of integers $0\le d_1\le d_2\le 2s+2$,
--   $$\sqrt{\frac{d_1!}{d_2!}}\Big(\frac{T}{2\sigma^2}\Big)^{d_2-d_1}\le\frac{a_{d_2}(\sigma^2)}{a_{d_1}(\sigma^2)}\le\sqrt{\frac{d_1!}{d_2!}}\Big(\frac{T+1}{\sigma^2}\Big)^{d_2-d_1}.$$
--
--   These estimates control the weights $\lambda_i^{(2r)}$ and the scaled regressors $a_i$, and are used in Lemmas 5.8, 5.9 and Theorem 5.1(iv).
--
--   **Formalization Note** $a_d$ is `coeff T d`, with the threshold $T$ an explicit argument.
--
--   Differences from the source:
--   - encoding: a_d(σ²), with T implicit → coeff T d σ², with T an explicit argument; reason: the coefficient depends on T; T is the lemma's own free threshold
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Lemma 5.7, (30), p.22 (PDF pp.25–26)

import Mathlib
import Definitions.Def_SelfSelReg_hypK
import Definitions.Def_SelfSelReg_restrictedMoment

namespace SelfSelReg

/-- **Lemma 5.7** (Restricted Moment Coefficient Estimates).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Lemma 5.7, p.22 (PDF pp.25–26): "Use the choice of K from
Hyperparameters 4.1. Let s ≥ 1 be an integer and suppose T > 0 and T² ≥ Ks. For every
σ² ∈ [1 + ∆², 1 + B²], the coefficients a_d(σ²) are positive for 0 ≤ d ≤ 2s + 2. Moreover, for every
pair of integers 0 ≤ d₁ ≤ d₂ ≤ 2s + 2,
√(d₁!/d₂!) (T/(2σ²))^{d₂−d₁} ≤ a_{d₂}(σ²)/a_{d₁}(σ²) ≤ √(d₁!/d₂!) ((T + 1)/σ²)^{d₂−d₁}." (30)

**Formalization Note.** `K = hypK B ∆`, with `B ≥ 1`, `∆ ∈ (0, 1]` the constants of Assumption 1.2;
`s` and `T` are free, as on the page. `a_d` is `coeff T d` (17). The exponent `d₂ − d₁` is a natural
number (`d₁ ≤ d₂`). -/
theorem lemma_5_7 (B Δ : ℝ) (hB : 1 ≤ B) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (s : ℕ) (hs : 1 ≤ s) (T : ℝ)
    (hT : 0 < T) (hTs : hypK B Δ * s ≤ T ^ 2) (σsq : ℝ) (hσ : 1 + Δ ^ 2 ≤ σsq)
    (hσ' : σsq ≤ 1 + B ^ 2) :
    (∀ d : ℕ, d ≤ 2 * s + 2 → 0 < coeff T d σsq) ∧
      ∀ d₁ d₂ : ℕ, d₁ ≤ d₂ → d₂ ≤ 2 * s + 2 →
        Real.sqrt ((d₁.factorial : ℝ) / d₂.factorial) * (T / (2 * σsq)) ^ (d₂ - d₁) ≤
            coeff T d₂ σsq / coeff T d₁ σsq ∧
          coeff T d₂ σsq / coeff T d₁ σsq ≤
            Real.sqrt ((d₁.factorial : ℝ) / d₂.factorial) * ((T + 1) / σsq) ^ (d₂ - d₁) := by sorry

end SelfSelReg
