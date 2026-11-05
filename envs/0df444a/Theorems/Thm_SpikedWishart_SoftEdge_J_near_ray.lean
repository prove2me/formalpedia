-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_J_near_ray
-- name    : SpikedWishart.SoftEdge.J_near_ray
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-04T06:27:35.968525+00:00
-- url     : https://prove2.me/theorems/356537ce-026f-426e-ab01-44603f20a3ab
-- title:
--   Near $p_c$ the rescaled $\mathcal J$-integral over the ray $p+te^{i\theta}$ is the Airy-type limit up to $O(e^{-\varepsilon v}/M^{1/3})$
-- statement:
--   Let $\varepsilon>0$, $\cos\theta=-1/2$, $\sin^2\theta=3/4$, $C_1,K_2\ge0$, $\delta>0$. There is $B\ge0$ such that under the cubic Taylor and ratio bounds near $p_c$ (as in the statement), the rescaled ray integral of $h_J/Z_M$ differs from $\frac{e^{\varepsilon v}}{2\pi}\int_0^\infty\varphi_J(\cdot)$, $\varphi_J(a)=e^{va-a^3/3}a^k$, by at most
--
--   $$\frac{Be^{-\varepsilon v}}{m}.$$
--
--   Role: the main-term estimate of part (ii). Notation as in the paper: $f=f_{\gamma,q}$ is the phase function, $p_c$ the double critical point, $\nu=\nu(\gamma)$, $g$ the spike factor $\prod_{j>k}(\pi_j-z)$-type product of (103), $Z_M$ the normalisation (116), and $\mathcal H$-integrand $h_H(z)=e^{-\sigma u(z-q)}e^{Mf(z)}(p_c-z)^{-k}g(z)^{-1}$, $\sigma=\nu M^{1/3}$; $\mathcal J$-integrand $h_J(z)=e^{\sigma v(z-q)}e^{-Mf(z)}(p_c-z)^{k}g(z)$.
-- source:
--   J. Baik, G. Ben Arous and S. Peche, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), https://doi.org/10.1214/009117905000000233, the local analysis near $p_c$ for $\mathcal J$, proof of Proposition 3.1, pp. 1661-1664

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open Complex MeasureTheory

namespace SpikedWishart.SoftEdge

theorem J_near_ray :
    ∀ (ε V₀ C₁ K₂ δ₀ δ θ : ℝ) (k : ℕ), 0 < ε → Real.cos θ = -(1 / 2) →
    Real.sin θ ^ 2 = 3 / 4 → 0 ≤ C₁ → 0 ≤ K₂ → 0 < δ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {r : ℕ} (π : Fin r → ℝ) (γ q v m σ : ℝ) (M : ℕ),
      V₀ ≤ v → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ nu γ → nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ →
      σ = nu γ * m → q = pc γ - ε / σ → δ + 2 * ε / σ ≤ δ₀ →
      (C₁ + 2 * K₂) * (nu γ * δ + 2 * ε / m) ≤ 1 / 8 →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → ‖fFn γ q z - fFn γ q (pc γ) -
          ((nu γ ^ 3 / 3 : ℝ) : ℂ) * (z - pc γ) ^ 3‖ ≤ C₁ * ‖z - pc γ‖ ^ 4) →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → gFn k π z ≠ 0 ∧
          ‖gFn k π (pc γ) / gFn k π z - 1‖ ≤ K₂ * ‖z - pc γ‖) →
      gFn k π (pc γ) ≠ 0 →
      ContinuousOn ((fun z : ℂ => exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (z - q)) * exp (-(M : ℂ) * fFn γ q z) * (((pc γ : ℂ) - z) ^ k * gFn k π z))) (Metric.closedBall (pc γ : ℂ) δ₀) →
      ‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t in (0 : ℝ)..δ, (exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * ((((pc γ + (-2 * ε) / σ : ℝ) : ℂ) +
            (t : ℂ) * exp ((θ : ℂ) * I)) - q)) * exp (-(M : ℂ) * fFn γ q (((pc γ + (-2 * ε) / σ : ℝ) : ℂ) +
            (t : ℂ) * exp ((θ : ℂ) * I))) * (((pc γ : ℂ) - (((pc γ + (-2 * ε) / σ : ℝ) : ℂ) +
            (t : ℂ) * exp ((θ : ℂ) * I))) ^ k * gFn k π (((pc γ + (-2 * ε) / σ : ℝ) : ℂ) +
            (t : ℂ) * exp ((θ : ℂ) * I)))) * exp ((θ : ℂ) * I)) -
        ((Real.exp (ε * v) / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ τ in Set.Ioi (0 : ℝ), (exp ((v : ℂ) * (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) - (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) ^ 3 / 3) * (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) ^ k) *
            exp ((θ : ℂ) * I)‖ ≤
        B * Real.exp (-ε * v) / m := by sorry

end SpikedWishart.SoftEdge
