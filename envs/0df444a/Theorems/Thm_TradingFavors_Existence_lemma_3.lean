-- Prove2me | Theorems.Thm_TradingFavors_Existence_lemma_3
-- name    : TradingFavors.Existence.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:16.146066+00:00
-- url     : https://prove2.me/theorems/d931652e-e60b-4eb9-895b-d4ca35a8b4f1
-- title:
--   Lemma 3, p. 12 (PDF 12) — recursions (8)–(10) for v₁(k|σ), α₁, α, β, β₂ ∈ (0,1), α + β < 1, intercepts (11)–(13)
-- statement:
--   Fix parameters satisfying the standing assumptions, a strategy profile $\sigma$ and $k\in\mathbb Z$, and write $v_1(k)=\pi_1(1,1,k\mid\sigma)$. Then
--   $$
--   \begin{aligned}
--   v_1(k)&=\alpha_1\,v_1(k+1)+\underline r_1 &&\text{if }\sigma_1(k)=0,\ \sigma_2(k)=1, &(8)\\
--   v_1(k)&=\beta\,v_1(k-1)+\alpha\,v_1(k+1)+r_1 &&\text{if }\sigma_1(k)=0,\ \sigma_2(k)=0, &(9)\\
--   v_1(k)&=\beta_2\,v_1(k-1)+\overline r_1 &&\text{if }\sigma_1(k)=1,\ \sigma_2(k)=0. &(10)
--   \end{aligned}
--   $$
--   Here $\alpha_1$ and $\alpha$ are the (4,3) entries of $\lambda_2B_1^{-1}(k\mid\sigma)$ in the cases of (8) and (9), and $\beta$ and $\beta_2$ are the (4,2) entries of $\lambda_1B_1^{-1}(k\mid\sigma)$ in the cases of (9) and (10). Moreover:
--
--   1. $\alpha_1,\alpha,\beta,\beta_2\in(0,1)$ and $\alpha+\beta<1$;
--   2. in each case the fourth entry of $B_1^{-1}(k\mid\sigma)R_1(k\mid\sigma)$ equals the corresponding intercept, where
--   $$
--   \underline r_1=\pi_1^{NC}(1)-\alpha_1\pi_1^{NC}(0)-\alpha_1l_1,\quad r_1=(1-\beta)\pi_1^{NC}(1)-\alpha\pi_1^{NC}(0)-\alpha l_1+\beta q_1,\quad \overline r_1=(1-\beta_2)\pi_1^{NC}(1)+\beta_2q_1 .
--   $$
--
--   The coefficients are discount factors of first passages out of cluster $k$; the recursions link the values $v_1(k)$ across clusters and drive every later result.
--
--   **Formalization Note** The printed lemma assigns $\beta_2$ to (9) and $\beta$ to (10); the proof (p. A2) and (13) use $\beta$ in (9) and $\beta_2$ in (10), which is what is stated. The coefficients are defined as the matrix entries, not by any closed form.
-- source:
--   Hu & Caldentey, Trust and Reciprocity in Firms’ Capacity Sharing, SSRN 4348127 (version of February 6, 2023), p. 12 (PDF 12), Lemma 3, eqs. (8)–(13); proof pp. A1–A3 (PDF 31–33)

import Mathlib
import Definitions.Def_TradingFavors_Existence_Model

namespace TradingFavors.Existence

open Matrix

theorem lemma_3 (θ : Params) (hθ : θ.Standing) (σ : Profile) (k : ℤ) :
    (σ.s1 k = 0 → σ.s2 k = 1 → v1 θ σ k = alpha1 θ * v1 θ σ (k + 1) + rLow1 θ) ∧
    (σ.s1 k = 0 → σ.s2 k = 0 →
      v1 θ σ k = beta θ * v1 θ σ (k - 1) + alpha θ * v1 θ σ (k + 1) + rMid1 θ) ∧
    (σ.s1 k = 1 → σ.s2 k = 0 → v1 θ σ k = beta2 θ * v1 θ σ (k - 1) + rBar1 θ) ∧
    (0 < alpha1 θ ∧ alpha1 θ < 1) ∧ (0 < alpha θ ∧ alpha θ < 1) ∧
    (0 < beta θ ∧ beta θ < 1) ∧ (0 < beta2 θ ∧ beta2 θ < 1) ∧
    alpha θ + beta θ < 1 ∧
    (σ.s1 k = 0 → σ.s2 k = 1 → ((B1 θ 0 1)⁻¹ *ᵥ R1vec θ σ k) 3 = rLow1 θ) ∧
    (σ.s1 k = 0 → σ.s2 k = 0 → ((B1 θ 0 0)⁻¹ *ᵥ R1vec θ σ k) 3 = rMid1 θ) ∧
    (σ.s1 k = 1 → σ.s2 k = 0 → ((B1 θ 1 0)⁻¹ *ᵥ R1vec θ σ k) 3 = rBar1 θ) := by sorry

end TradingFavors.Existence
