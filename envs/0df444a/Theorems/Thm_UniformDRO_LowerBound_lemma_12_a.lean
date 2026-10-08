-- Prove2me | Theorems.Thm_UniformDRO_LowerBound_lemma_12_a
-- name    : UniformDRO.LowerBound.lemma_12_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:06:51.992376+00:00
-- url     : https://prove2.me/theorems/43509409-4093-40b1-b289-61aaae8a4410
-- title:
--   Lemma 12 (first claim), p. 45 — for p ≥ p_k the robust risk of a two-point Z is its larger value z₁
-- statement:
--   Let $k > 1$, $\rho > 0$, $c_k = (1 + k(k-1)\rho)^{1/k}$ and $p_k = c_k^{-k/(k-1)}$. Let $z_0 \le z_1$, $p \in [0,1]$, and let $Z$ take the value $z_0$ with probability $1-p$ and $z_1$ with probability $p$. If $p \ge p_k$, then
--   $$\mathcal R_k(Z) = z_1.$$
--
--   So once the larger value has mass at least $p_k$, the Cressie–Read ball of radius $\rho$ contains the point mass at $z_1$, and the worst case is the largest value of $Z$.
--
--   **Formalization Note.** $\mathcal R_k(Z)$ is the robust risk of the two-point law $(1-p)\delta_{z_0} + p\delta_{z_1}$ in the likelihood-ratio form (3) of the mission's definition file.
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, Lemma 12 (first claim), p. 45; proof App. D.1.1, pp. 46–47

import Mathlib
import Definitions.Def_UniformDRO_LowerBound_Setting

namespace UniformDRO.LowerBound

theorem lemma_12_a (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (z₀ z₁ p : ℝ) (hz : z₀ ≤ z₁)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hpk : pk k ρ ≤ p) :
    UniformDRO.Concentration.robustRisk k ρ (twoPointLaw z₀ z₁ p) id = z₁ := by sorry

end UniformDRO.LowerBound
