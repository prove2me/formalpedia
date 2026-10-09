-- Prove2me | Theorems.Thm_SphereGRF_HeatEq_lemma_7_2
-- name    : SphereGRF.HeatEq.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:35:57.356455+00:00
-- url     : https://prove2.me/theorems/a1257a56-85ad-4cdb-83a0-bb72e5bb44b0
-- title:
--   Lemma 7.2, pp. 41–43 (as proved) — ‖X(t) − X^κ(t)‖_{L^p(Ω;L²)} ≤ Ĉ_p κ^{−α/2} + e^{−(κ+1)(κ+2)t}‖X₀‖_{L^{max(p,2)}}
-- statement:
--   Fix $p>0$, $C>0$ and $\alpha>0$. There is a constant $\hat C_p$, depending only on $p$, $C$ and $\alpha$, with the following property.
--
--   Let $(\Omega,\mathcal A,\mathbb P)$ be a probability space, $(A_\ell)_{\ell\ge0}$ a nonnegative angular power spectrum and $\ell_0\in\mathbb N=\{1,2,\dots\}$ with $A_\ell\le C\ell^{-\alpha}$ for all $\ell>\ell_0$, let $\beta^i_{\ell m}$ be independent real Brownian motions and $X_0$ a jointly measurable random field with $\mathbb E\|X_0\|^2_{L^2(\mathbb S^2)}<\infty$. Let $X(t)$ be the spectral solution of the stochastic heat equation $dX=\Delta_{\mathbb S^2}X\,dt+dW$ with $X(0)=X_0$ and $X^\kappa(t)$ its truncation at degree $\kappa$. Then for every $t>0$ and every $\kappa\ge\ell_0$,
--   $$\|X(t)-X^\kappa(t)\|_{L^p(\Omega;L^2(\mathbb S^2))}\le\hat C_p\,\kappa^{-\alpha/2}+e^{-(\kappa+1)(\kappa+2)t}\,\|X_0\|_{L^{\max(p,2)}(\Omega;L^2(\mathbb S^2))}.$$
--
--   Here $\|Z\|_{L^q(\Omega;L^2(\mathbb S^2))}=(\mathbb E\|Z\|^q_{L^2(\mathbb S^2)})^{1/q}$ (a quasi-norm for $q<1$). The $L^p$ bound for all $p$ is what turns the mean-square estimate into almost sure convergence (Corollary 7.3).
--
--   **Formalization Note.** The paper's Lemma 7.2 states $\hat C_p\kappa^{-\alpha/2}$ uniformly in time with $\hat C_p$ depending on $\|X_0\|_{L^{\max(p,2)}}$, $p$, $C$, $\alpha$; its proof (p. 43) bounds the initial-condition tail by $e^{-(\kappa+1)(\kappa+2)t}\|X_0\|_{L^p}$ and then absorbs it into $C\kappa^{-\alpha/2}$ with a constant depending on $t$, so the printed uniformity in time does not follow (and fails for general $X_0$). The Lean states the bound the proof establishes: $\hat C_p$ is chosen before the probability space, the spectrum, $\ell_0$, the noise, $X_0$, $t$ and $\kappa$, and the dependence on $X_0$ is the explicit second term. No independence of $X_0$ from the noise is assumed. The quantities are in $[0,\infty]$.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, Lemma 7.2, p. 41, and its proof, pp. 41–43

import Mathlib
import Definitions.Def_SphereGRF_HeatEq_Setting

namespace SphereGRF.HeatEq

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

universe u

/-- Lemma 7.2, pp. 41–43, in the form its proof establishes: for every `p > 0` there is a constant
`Ĉ_p`, depending only on `p, C, α`, such that the `L^p(Ω; L²(S²))` truncation error of `X^κ(t)` is at most
`Ĉ_p κ^{-α/2} + e^{-(κ+1)(κ+2)t} ‖X₀‖_{L^{max(p,2)}(Ω; L²(S²))}` for all `t > 0` and `κ ≥ ℓ₀`. -/
theorem lemma_7_2 (p C α : ℝ) (hp : 0 < p) (hC : 0 < C) (hα : 0 < α) :
    ∃ Cp : ℝ, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (A : ℕ → ℝ) (ℓ₀ : ℕ), (∀ ℓ, 0 ≤ A ℓ) → 1 ≤ ℓ₀ →
      (∀ ℓ : ℕ, ℓ₀ < ℓ → A ℓ ≤ C * (ℓ : ℝ) ^ (-α)) →
      ∀ (B : ℕ → ℕ → Fin 2 → ℝ≥0 → Ω → ℝ), (∀ ℓ m i, IsBrownianReal (B ℓ m i) P) →
      iIndepFun (fun q : ℕ × ℕ × Fin 2 => fun ω (t : ℝ≥0) => B q.1 q.2.1 q.2.2 t ω) P →
      ∀ (X₀ : Ω → S2 → ℝ), Measurable (fun q : Ω × S2 => X₀ q.1 q.2) →
      ∫⁻ ω, l2S2Sq (X₀ ω) ∂P < ∞ →
      ∀ t : ℝ≥0, 0 < t → ∀ κ : ℕ, ℓ₀ ≤ κ →
        lpL2Norm P p (fun ω y => heatSol A B X₀ t ω y - heatTrunc A B X₀ κ t ω y) ≤
          ENNReal.ofReal (Cp * (κ : ℝ) ^ (-α / 2))
            + ENNReal.ofReal (Real.exp (-(((κ : ℝ) + 1) * ((κ : ℝ) + 2) * t)))
              * lpL2Norm P (max p 2) X₀ := by sorry

end SphereGRF.HeatEq
