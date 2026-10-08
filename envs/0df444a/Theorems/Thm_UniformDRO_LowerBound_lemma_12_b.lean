-- Prove2me | Theorems.Thm_UniformDRO_LowerBound_lemma_12_b
-- name    : UniformDRO.LowerBound.lemma_12_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:07:56.399244+00:00
-- url     : https://prove2.me/theorems/174b5fd1-bdb7-4bd2-8cbe-710138eadc11
-- title:
--   Lemma 12 (second claim), p. 45 — for p ≤ p_k, R_k(Z) ≤ c_k p^{1/k*} z₁ + (1 − c_k p^{1/k*}) z₀
-- statement:
--   Let $k > 1$, $\rho > 0$, $k_* = k/(k-1)$, $c_k = (1 + k(k-1)\rho)^{1/k}$ and $p_k = c_k^{-k/(k-1)}$. Let $z_0 \le z_1$, $p \in [0,1]$, and let $Z = z_0$ with probability $1-p$ and $Z = z_1$ with probability $p$. If $p \le p_k$, then
--   $$\mathcal R_k(Z) \le c_k\, p^{1/k_*}\, z_1 + \bigl(1 - c_k\, p^{1/k_*}\bigr) z_0 .$$
--
--   For $p \le p_k$ the weight $c_k p^{1/k_*}$ is at most $1$, so the bound says that the worst-case distribution moves at most a fraction $c_k p^{1/k_*}$ of the mass to $z_1$. In the proof of Theorem 3 this bounds the robust risk of the law with mass $p_k - \delta$ at $M$.
--
--   **Formalization Note.** Real powers are `Real.rpow`; at $p = 0$ the bound reads $\mathcal R_k(Z) \le z_0$.
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, Lemma 12 (second claim), p. 45; proof App. D.1.1, pp. 46–47

import Mathlib
import Definitions.Def_UniformDRO_LowerBound_Setting

namespace UniformDRO.LowerBound

theorem lemma_12_b (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (z₀ z₁ p : ℝ) (hz : z₀ ≤ z₁)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hpk : p ≤ pk k ρ) :
    UniformDRO.Concentration.robustRisk k ρ (twoPointLaw z₀ z₁ p) id ≤
      UniformDRO.Concentration.ck k ρ * p ^ (1 / UniformDRO.Concentration.kstar k) * z₁ + (1 - UniformDRO.Concentration.ck k ρ * p ^ (1 / UniformDRO.Concentration.kstar k)) * z₀ := by sorry

end UniformDRO.LowerBound
