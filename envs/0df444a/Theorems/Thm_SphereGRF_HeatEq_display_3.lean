-- Prove2me | Theorems.Thm_SphereGRF_HeatEq_display_3
-- name    : SphereGRF.HeatEq.display_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:35:04.92923+00:00
-- url     : https://prove2.me/theorems/e5b575fd-bc6b-4133-85f9-fc731df784b0
-- title:
--   §7, display (3), p. 36 — ∫₀ᵗ e^{−ℓ(ℓ+1)(t−s)} dβ(s) is N(0, (2ℓ(ℓ+1))^{−1}(1 − e^{−2ℓ(ℓ+1)t})) for ℓ ≥ 1
-- statement:
--   Let $\beta$ be a real-valued standard Brownian motion on a probability space $(\Omega,\mathcal A,\mathbb P)$, let $\ell\ge1$ be an integer and $t\ge0$. Then the stochastic convolution
--   $$\int_0^te^{-\ell(\ell+1)(t-s)}\,d\beta(s)\ \sim\ \mathcal N\Big(0,\ \frac{1-e^{-2\ell(\ell+1)t}}{2\ell(\ell+1)}\Big).$$
--
--   This is the distributional fact behind the exact simulation of the stochastic heat equation on the sphere: each spectral mode of the noise part of the solution is an Ornstein–Uhlenbeck variable with this variance, and the variances $\sigma^2_{\ell t}\le(2\ell(\ell+1))^{-1}$ produce the extra decay $\ell^{-2}$ used in Lemmas 7.1 and 7.2.
--
--   **Formalization Note.** The stochastic integral is the pathwise expression $\beta(t)-\lambda\int_0^te^{-\lambda(t-s)}\beta(s)\,ds$ with $\lambda=\ell(\ell+1)$, which equals the Itô (Wiener) integral almost surely by integration by parts (see the Setting file). The law is stated as the pushforward of $\mathbb P$, equal to Mathlib's `gaussianReal 0 v`. The page states the claim for the Brownian motions $\beta^i_{\ell m}$, $m=1,\dots,\ell$, $i=1,2$; the Lean states it for an arbitrary real Brownian motion, which is the same claim.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, §7, display (3), p. 36

import Mathlib
import Definitions.Def_SphereGRF_HeatEq_Setting

namespace SphereGRF.HeatEq

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Display (3), p. 36: for `ℓ ≥ 1` the stochastic convolution `∫₀ᵗ e^{-ℓ(ℓ+1)(t-s)} dβ(s)` of a real
Brownian motion `β` is `N(0, (2ℓ(ℓ+1))⁻¹ (1 - e^{-2ℓ(ℓ+1)t}))`. -/
theorem display_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (b : ℝ≥0 → Ω → ℝ) (hb : IsBrownianReal b P) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (t : ℝ≥0) :
    P.map (fun ω => ouConv (lam ℓ) (fun s => b s ω) t) =
      gaussianReal 0 ((1 - Real.exp (-2 * lam ℓ * t)) / (2 * lam ℓ)).toNNReal := by sorry

end SphereGRF.HeatEq
