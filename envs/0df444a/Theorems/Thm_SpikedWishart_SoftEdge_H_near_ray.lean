-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_H_near_ray
-- name    : SpikedWishart.SoftEdge.H_near_ray
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-04T07:53:30.617777+00:00
-- url     : https://prove2.me/theorems/38bd2854-c220-41b0-8723-791836ac0672
-- title:
--   Near $p_c$ the rescaled $\mathcal H$-integral over the ray $p+te^{i\theta}$ is the Airy-type limit up to $O(e^{-\varepsilon u/2}/M^{1/3})$
-- statement:
--   Let $\varepsilon>0$, $\cos\theta=1/2$, $\sin^2\theta=3/4$, $C_1,K_2\ge0$, $\delta>0$. There is $B\ge0$ such that, whenever $u\ge U_0$, $m^3=M$, $m\ge1$, $\nu\ge1$, $\sigma=\nu m$, $q=p_c-\varepsilon/\sigma$, the cubic Taylor bound $|f(z)-f(p_c)-\tfrac{\nu^3}{3}(z-p_c)^3|\le C_1|z-p_c|^4$ and the ratio bound $|g(p_c)/g(z)-1|\le K_2|z-p_c|$ hold on $|z-p_c|\le\delta_0$ (with the smallness conditions of the statement) and $h_H$ is continuous there,
--
--   $$\Big|Z_M\frac{\sigma}{2\pi}\int_0^\delta h_H\big(p_c-\tfrac{\varepsilon}{2\sigma}+te^{i\theta}\big)e^{i\theta}dt-\frac{e^{-\varepsilon u}}{2\pi}\int_0^\infty \varphi_H\big(-\tfrac\varepsilon2+\tau e^{i\theta}\big)e^{i\theta}d\tau\Big|\le\frac{Be^{-\varepsilon u/2}}{m},$$
--
--   with $\varphi_H(a)=e^{-ua+a^3/3}a^{-k}$.
--
--   Role: the main-term estimate of part (i) on each of the two rays at $p_c$. Notation as in the paper: $f=f_{\gamma,q}$ is the phase function, $p_c$ the double critical point, $\nu=\nu(\gamma)$, $g$ the spike factor $\prod_{j>k}(\pi_j-z)$-type product of (103), $Z_M$ the normalisation (116), and $\mathcal H$-integrand $h_H(z)=e^{-\sigma u(z-q)}e^{Mf(z)}(p_c-z)^{-k}g(z)^{-1}$, $\sigma=\nu M^{1/3}$; $\mathcal J$-integrand $h_J(z)=e^{\sigma v(z-q)}e^{-Mf(z)}(p_c-z)^{k}g(z)$.
-- source:
--   J. Baik, G. Ben Arous and S. Peche, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), https://doi.org/10.1214/009117905000000233, the local analysis near $p_c$ (rescaling $z=p_c+a/\sigma$), proof of Proposition 3.1, pp. 1661-1664

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open Complex MeasureTheory

namespace SpikedWishart.SoftEdge

theorem H_near_ray :
    ∀ (ε U₀ C₁ K₂ δ₀ δ θ : ℝ) (k : ℕ), 0 < ε → Real.cos θ = 1 / 2 →
    Real.sin θ ^ 2 = 3 / 4 → 0 ≤ C₁ → 0 ≤ K₂ → 0 < δ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {r : ℕ} (π : Fin r → ℝ) (γ q u m σ : ℝ) (M : ℕ),
      U₀ ≤ u → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ nu γ → nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ →
      σ = nu γ * m → q = pc γ - ε / σ → δ + ε / (2 * σ) ≤ δ₀ →
      (C₁ + K₂) * (nu γ * δ + ε / (2 * m)) ≤ 1 / 8 →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → ‖fFn γ q z - fFn γ q (pc γ) -
          ((nu γ ^ 3 / 3 : ℝ) : ℂ) * (z - pc γ) ^ 3‖ ≤ C₁ * ‖z - pc γ‖ ^ 4) →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → gFn k π z ≠ 0 ∧
          ‖gFn k π (pc γ) / gFn k π z - 1‖ ≤ K₂ * ‖z - pc γ‖) →
      ContinuousOn ((fun z : ℂ => exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * (z - q)) * exp ((M : ℂ) * fFn γ q z) * (1 / (((pc γ : ℂ) - z) ^ k * gFn k π z)))) (Metric.closedBall (pc γ : ℂ) δ₀ \ {(pc γ : ℂ)}) →
      ‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t in (0 : ℝ)..δ, (exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * ((((pc γ + (-ε / 2) / σ : ℝ) : ℂ) +
            (t : ℂ) * exp ((θ : ℂ) * I)) - q)) * exp ((M : ℂ) * fFn γ q (((pc γ + (-ε / 2) / σ : ℝ) : ℂ) +
            (t : ℂ) * exp ((θ : ℂ) * I))) * (1 / (((pc γ : ℂ) - (((pc γ + (-ε / 2) / σ : ℝ) : ℂ) +
            (t : ℂ) * exp ((θ : ℂ) * I))) ^ k * gFn k π (((pc γ + (-ε / 2) / σ : ℝ) : ℂ) +
            (t : ℂ) * exp ((θ : ℂ) * I))))) * exp ((θ : ℂ) * I)) -
        ((Real.exp (-ε * u) / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ τ in Set.Ioi (0 : ℝ), (exp (-(u : ℂ) * (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) + (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3) * (1 / (((-ε / 2 : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) ^ k)) *
            exp ((θ : ℂ) * I)‖ ≤
        B * Real.exp (-(ε / 2) * u) / m := by sorry

end SpikedWishart.SoftEdge
