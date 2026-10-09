-- Prove2me | Theorems.Thm_SphereGRF_HeatEq_lemma_7_1
-- name    : SphereGRF.HeatEq.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:42.666629+00:00
-- url     : https://prove2.me/theorems/9914e68b-bcfe-447e-8fdb-ea9fc8250017
-- title:
--   Lemma 7.1, pp. 39–40 (as proved) — E‖X(t) − X^κ(t)‖² ≤ C(2/α + 1/(α+1))κ^{−α} + e^{−2(κ+1)(κ+2)t}E‖X₀‖² for κ ≥ ℓ₀
-- statement:
--   Consider the stochastic heat equation $dX(t)=\Delta_{\mathbb S^2}X(t)\,dt+dW(t)$ on the unit sphere, with initial condition $X_0\in L^2(\Omega;L^2(\mathbb S^2))$ and an isotropic $Q$-Wiener process $W$ with angular power spectrum $(A_\ell)_{\ell\ge0}$, $A_\ell\ge0$, driven by independent real Brownian motions $\beta^i_{\ell m}$. Let $X(t)$ be its spectral solution and $X^\kappa(t)=\sum_{\ell=0}^{\kappa}X_\ell(t)$ the truncation at degree $\kappa$ (see the Setting definition). Assume:
--
--   1. there are $\ell_0\in\mathbb N=\{1,2,\dots\}$, $\alpha>0$ and $C>0$ with $A_\ell\le C\ell^{-\alpha}$ for all $\ell>\ell_0$;
--   2. the spherical-harmonic coefficients $\big((X_0,u)_{L^2(\mathbb S^2)}\big)_u$ of the initial condition (for $u$ in the real orthonormal basis) are independent of the driving Brownian motions.
--
--   Then for every $t>0$ and every $\kappa\ge\ell_0$,
--   $$\|X(t)-X^\kappa(t)\|^2_{L^2(\Omega;L^2(\mathbb S^2))}\le C\Big(\frac2\alpha+\frac1{\alpha+1}\Big)\kappa^{-\alpha}+e^{-2(\kappa+1)(\kappa+2)t}\,\|X_0\|^2_{L^2(\Omega;L^2(\mathbb S^2))}.$$
--
--   The first term is the truncation error of the noise part, a Gaussian random field with angular power spectrum $A_\ell(1-e^{-2\ell(\ell+1)t})/(2\ell(\ell+1))\le C\ell^{-(\alpha+2)}$; the second is the tail of the damped initial condition. In particular for $X_0=0$ the bound $\hat C^2\kappa^{-\alpha}$ with $\hat C^2=C(2/\alpha+1/(\alpha+1))$ holds uniformly in $t$.
--
--   **Formalization Note.** The paper's Lemma 7.1 states the bound $\hat C\kappa^{-\alpha/2}$ with $\hat C^2=\|X_0\|^2+C(2/\alpha+1/(\alpha+1))$ uniformly in time; this is false for nonzero $X_0$ (as $t\downarrow0$ the left side tends to the $L^2$ tail of $X_0$, which need not be $O(\kappa^{-\alpha})$). The Lean states the bound that the paper's proof establishes (p. 40, the two displayed bounds), keeping the explicit factor $e^{-2(\kappa+1)(\kappa+2)t}$. Hypothesis 2 is not printed in the lemma; the proof uses it when it drops the cross term ("$\mathbb E(\psi_\ell(j))=0$"), and it is implied by the usual assumption that $X_0$ is independent of $W$. The time partition of the page is not an argument: $X^\kappa(t)$ is defined from the solution formula, which the grid recursion reproduces exactly. The squared norm is $\mathbb E\int|\cdot|^2d\sigma$ in $[0,\infty]$; $X_0$ is assumed jointly measurable with $\mathbb E\|X_0\|^2<\infty$.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, Lemma 7.1, p. 39, and its proof, p. 40 (bound for ‖T − T^κ‖² and for the X₀ tail)

import Mathlib
import Definitions.Def_SphereGRF_HeatEq_Setting

namespace SphereGRF.HeatEq

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Lemma 7.1, pp. 39–40, in the form its proof establishes: the mean-square truncation error of the
spectral approximation `X^κ(t)` of the stochastic heat equation splits into the noise tail
`C (2/α + 1/(α+1)) κ^{-α}` and the initial-condition tail `e^{-2(κ+1)(κ+2)t} ‖X₀‖²`. -/
theorem lemma_7_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℕ → ℝ) (C α : ℝ) (ℓ₀ : ℕ)
    (hA0 : ∀ ℓ, 0 ≤ A ℓ) (hC : 0 < C) (hα : 0 < α) (hℓ₀ : 1 ≤ ℓ₀)
    (hdec : ∀ ℓ : ℕ, ℓ₀ < ℓ → A ℓ ≤ C * (ℓ : ℝ) ^ (-α))
    (B : ℕ → ℕ → Fin 2 → ℝ≥0 → Ω → ℝ)
    (hB : ∀ ℓ m i, IsBrownianReal (B ℓ m i) P)
    (hBind : iIndepFun (fun q : ℕ × ℕ × Fin 2 => fun ω (t : ℝ≥0) => B q.1 q.2.1 q.2.2 t ω) P)
    (X₀ : Ω → S2 → ℝ)
    (hX₀meas : Measurable (fun q : Ω × S2 => X₀ q.1 q.2))
    (hX₀L2 : ∫⁻ ω, l2S2Sq (X₀ ω) ∂P < ∞)
    (hX₀ind : IndepFun (fun ω => fun q : ℕ × ℕ × Fin 2 => coef X₀ ω q.1 q.2.1 q.2.2)
      (fun ω => fun (q : ℕ × ℕ × Fin 2) (s : ℝ≥0) => B q.1 q.2.1 q.2.2 s ω) P) :
    ∀ t : ℝ≥0, 0 < t → ∀ κ : ℕ, ℓ₀ ≤ κ →
      ∫⁻ ω, l2S2Sq (fun y => heatSol A B X₀ t ω y - heatTrunc A B X₀ κ t ω y) ∂P ≤
        ENNReal.ofReal (C * (2 / α + 1 / (α + 1)) * (κ : ℝ) ^ (-α))
          + ENNReal.ofReal (Real.exp (-2 * ((κ : ℝ) + 1) * ((κ : ℝ) + 2) * t))
            * ∫⁻ ω, l2S2Sq (X₀ ω) ∂P := by sorry

end SphereGRF.HeatEq
