-- Prove2me | Theorems.Thm_SphereGRF_HeatEq_corollary_7_3
-- name    : SphereGRF.HeatEq.corollary_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:55.338153+00:00
-- url     : https://prove2.me/theorems/4a41041f-7d03-4f1d-9c2e-29f869482a88
-- title:
--   Corollary 7.3, p. 43 — for each t > 0 and β < α/2, a.s. ‖X(t) − X^κ(t)‖_{L²(S²)} ≤ κ^{−β} for all large κ
-- statement:
--   Let $(\Omega,\mathcal A,\mathbb P)$ be a probability space and consider the stochastic heat equation on the unit sphere $\mathbb S^2$,
--   $$dX(t)=\Delta_{\mathbb S^2}X(t)\,dt+dW(t),\qquad X(0)=X_0\in L^2(\Omega;L^2(\mathbb S^2)),$$
--   where $W$ is an isotropic $Q$-Wiener process with nonnegative angular power spectrum $(A_\ell)_{\ell\ge0}$, driven by independent real Brownian motions $\beta^i_{\ell m}$. Let $X(t)=\sum_{\ell\ge0}X_\ell(t)$ be its spectral solution and $X^\kappa(t)=\sum_{\ell=0}^{\kappa}X_\ell(t)$ the approximation obtained by truncating at degree $\kappa$. Assume there are $\ell_0\in\mathbb N=\{1,2,\dots\}$, $\alpha>0$ and a constant $C$ with
--   $$A_\ell\le C\,\ell^{-\alpha}\qquad\text{for all }\ell>\ell_0 .$$
--   Then for every $t>0$ and every $\beta<\alpha/2$, almost surely
--   $$\|X(t)-X^\kappa(t)\|_{L^2(\mathbb S^2)}\le\kappa^{-\beta}\qquad\text{for all sufficiently large }\kappa .$$
--
--   This is the pathwise convergence rate of the spectral method for the stochastic heat equation on the sphere; it justifies simulating one path by the truncated series and is the SPDE analogue of the almost sure convergence of truncated Karhunen–Loève expansions of isotropic Gaussian random fields.
--
--   **Formalization Note.** The threshold beyond which the bound holds depends on $\omega$ and on $t$; the paper's phrase "uniformly in time" is not formalized (the statement is for each fixed $t>0$). The time partition $0=t_0<\dots<t_n=t$ of the page is not an argument: $n\in\mathbb N$ forces $t>0$, and $X^\kappa(t)$ is defined from the solution formula, which the recursion on any grid reproduces, so independence of the discretization is automatic. The inequality is stated for the squares, $\|\cdot\|^2_{L^2(\mathbb S^2)}\le(\kappa^{-\beta})^2$, in $[0,\infty]$. $X_0$ is assumed jointly measurable in $(\omega,y)$ with $\mathbb E\|X_0\|^2_{L^2(\mathbb S^2)}<\infty$; no independence between $X_0$ and $W$ is needed.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, Corollary 7.3, p. 43

import Mathlib
import Definitions.Def_SphereGRF_HeatEq_Setting

namespace SphereGRF.HeatEq

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

/-- Corollary 7.3, p. 43: for every fixed `t > 0` and every `β < α/2`, almost surely
`‖X(t) - X^κ(t)‖_{L²(S²)} ≤ κ^{-β}` for all sufficiently large `κ`. -/
theorem corollary_7_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℕ → ℝ) (C α : ℝ) (ℓ₀ : ℕ)
    (hA0 : ∀ ℓ, 0 ≤ A ℓ) (hα : 0 < α) (hℓ₀ : 1 ≤ ℓ₀)
    (hdec : ∀ ℓ : ℕ, ℓ₀ < ℓ → A ℓ ≤ C * (ℓ : ℝ) ^ (-α))
    (B : ℕ → ℕ → Fin 2 → ℝ≥0 → Ω → ℝ)
    (hB : ∀ ℓ m i, IsBrownianReal (B ℓ m i) P)
    (hBind : iIndepFun (fun q : ℕ × ℕ × Fin 2 => fun ω (t : ℝ≥0) => B q.1 q.2.1 q.2.2 t ω) P)
    (X₀ : Ω → S2 → ℝ)
    (hX₀meas : Measurable (fun q : Ω × S2 => X₀ q.1 q.2))
    (hX₀L2 : ∫⁻ ω, l2S2Sq (X₀ ω) ∂P < ∞) :
    ∀ t : ℝ≥0, 0 < t → ∀ β : ℝ, β < α / 2 →
      ∀ᵐ ω ∂P, ∀ᶠ κ : ℕ in atTop,
        l2S2Sq (fun y => heatSol A B X₀ t ω y - heatTrunc A B X₀ κ t ω y) ≤
          ENNReal.ofReal ((κ : ℝ) ^ (-β)) ^ 2 := by sorry

end SphereGRF.HeatEq
