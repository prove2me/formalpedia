-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_J_conn_piece
-- name    : SpikedWishart.SoftEdge.J_conn_piece
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-04T06:28:08.846284+00:00
-- url     : https://prove2.me/theorems/37feb1a3-1303-45c5-a064-f2abbc1e1878
-- title:
--   The short horizontal connector of the $\mathcal J$-contour contributes $O(e^{-\varepsilon v}/M^{1/3})$
-- statement:
--   Under the local hypotheses of the near-ray estimate for $\mathcal J$, together with $\sigma\delta\ge1$, the horizontal connector integral of $h_J/Z_M$, scaled by $\sigma/(2\pi)$, is at most
--
--   $$\frac{Be^{-\varepsilon v}}{m}.$$
--
--   Role: bounds the connector pieces of part (ii). Notation as in the paper: $f=f_{\gamma,q}$ is the phase function, $p_c$ the double critical point, $\nu=\nu(\gamma)$, $g$ the spike factor $\prod_{j>k}(\pi_j-z)$-type product of (103), $Z_M$ the normalisation (116), and $\mathcal H$-integrand $h_H(z)=e^{-\sigma u(z-q)}e^{Mf(z)}(p_c-z)^{-k}g(z)^{-1}$, $\sigma=\nu M^{1/3}$; $\mathcal J$-integrand $h_J(z)=e^{\sigma v(z-q)}e^{-Mf(z)}(p_c-z)^{k}g(z)$.
-- source:
--   J. Baik, G. Ben Arous and S. Peche, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), https://doi.org/10.1214/009117905000000233, the local analysis near $p_c$ for $\mathcal J$, proof of Proposition 3.1, pp. 1661-1664

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open Complex MeasureTheory

namespace SpikedWishart.SoftEdge

theorem J_conn_piece :
    ∀ (ε V₀ C₁ K₂ δ₀ δ θ : ℝ) (k : ℕ), 0 < ε → Real.cos θ = -(1 / 2) →
    Real.sin θ ^ 2 = 3 / 4 → 0 ≤ C₁ → 0 ≤ K₂ → 0 < δ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {r : ℕ} (π : Fin r → ℝ) (γ q v m σ : ℝ) (M : ℕ),
      V₀ ≤ v → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ nu γ → nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ →
      σ = nu γ * m → q = pc γ - ε / σ → δ + 2 * ε / σ ≤ δ₀ →
      (C₁ + 2 * K₂) * (nu γ * δ + 2 * ε / m) ≤ 1 / 8 → 4 * ε ≤ σ * δ →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → ‖fFn γ q z - fFn γ q (pc γ) -
          ((nu γ ^ 3 / 3 : ℝ) : ℂ) * (z - pc γ) ^ 3‖ ≤ C₁ * ‖z - pc γ‖ ^ 4) →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → gFn k π z ≠ 0 ∧
          ‖gFn k π (pc γ) / gFn k π z - 1‖ ≤ K₂ * ‖z - pc γ‖) →
      gFn k π (pc γ) ≠ 0 →
      ‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ s in (0 : ℝ)..(pc γ - (pc γ + (-2 * ε) / σ)), (fun z : ℂ => exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (z - q)) * exp (-(M : ℂ) * fFn γ q z) * (((pc γ : ℂ) - z) ^ k * gFn k π z))
            (((pc γ + (-2 * ε) / σ : ℝ) : ℂ) + (δ : ℂ) * exp ((θ : ℂ) * I) + (s : ℂ))‖ ≤
        B * Real.exp (-ε * v) / m := by sorry

end SpikedWishart.SoftEdge
