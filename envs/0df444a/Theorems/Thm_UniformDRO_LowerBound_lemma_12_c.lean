-- Prove2me | Theorems.Thm_UniformDRO_LowerBound_lemma_12_c
-- name    : UniformDRO.LowerBound.lemma_12_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:07:19.280639+00:00
-- url     : https://prove2.me/theorems/0bd8206e-9854-4287-a81a-800101bd3c45
-- title:
--   Lemma 12 (third claim), p. 45 — if p ≤ p_k ∧ (1 − (1−β)^{1−k*} p_k), R_k(Z) ≥ β^{1/k} c_k p^{1/k*} z₁ + (1 − β^{1/k} c_k p^{1/k*}) z₀
-- statement:
--   Let $k > 1$, $\rho > 0$, $k_* = k/(k-1)$, $c_k = (1 + k(k-1)\rho)^{1/k}$ and $p_k = c_k^{-k/(k-1)}$. Let $z_0 \le z_1$, $p \in [0,1]$, and let $Z = z_0$ with probability $1-p$ and $Z = z_1$ with probability $p$. If, for some $\beta \in (0,1)$,
--   $$p \le p_k \wedge \bigl(1 - (1-\beta)^{1-k_*} p_k\bigr),$$
--   then
--   $$\mathcal R_k(Z) \ge \beta^{1/k} c_k\, p^{1/k_*}\, z_1 + \bigl(1 - \beta^{1/k} c_k\, p^{1/k_*}\bigr) z_0 .$$
--
--   Together with the second claim this pins the robust risk of a two-point law with small mass $p$ at its larger value to within a constant factor of $c_k p^{1/k_*}(z_1 - z_0)$ above $z_0$. It gives the separation in the $n^{-1/k_*}$ branch of Theorem 3.
--
--   **Formalization Note.** $\beta$ is arbitrary in $(0,1)$, as on the page; Theorem 3 uses $\beta = \beta_k$. Real powers are `Real.rpow`; the base $1 - \beta$ of the negative power $1 - k_*$ is positive.
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, Lemma 12 (third claim), p. 45; proof App. D.1.1, p. 47

import Mathlib
import Definitions.Def_UniformDRO_LowerBound_Setting

namespace UniformDRO.LowerBound

theorem lemma_12_c (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (z₀ z₁ p : ℝ) (hz : z₀ ≤ z₁)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hp1 : p ≤ pk k ρ)
    (hp2 : p ≤ 1 - (1 - β) ^ (1 - UniformDRO.Concentration.kstar k) * pk k ρ) :
    β ^ (1 / k) * UniformDRO.Concentration.ck k ρ * p ^ (1 / UniformDRO.Concentration.kstar k) * z₁ +
        (1 - β ^ (1 / k) * UniformDRO.Concentration.ck k ρ * p ^ (1 / UniformDRO.Concentration.kstar k)) * z₀ ≤
      UniformDRO.Concentration.robustRisk k ρ (twoPointLaw z₀ z₁ p) id := by sorry

end UniformDRO.LowerBound
