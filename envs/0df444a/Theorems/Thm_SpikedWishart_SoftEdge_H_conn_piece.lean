-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_H_conn_piece
-- name    : SpikedWishart.SoftEdge.H_conn_piece
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-04T07:53:55.814198+00:00
-- url     : https://prove2.me/theorems/dcad6916-8e1d-4363-8d4d-e99bbf3d3259
-- title:
--   The short horizontal connector of the $\mathcal H$-contour contributes $O(e^{-\varepsilon u/2}/M^{1/3})$
-- statement:
--   Under the same local hypotheses as the near-ray estimate, together with $\sigma\delta\ge1$, there is $B\ge0$ with
--
--   $$\Big|Z_M\frac{\sigma}{2\pi}\int_0^{\varepsilon/(2\sigma)}h_H\big(p_c-\tfrac{\varepsilon}{2\sigma}+\delta e^{i\theta}+s\big)ds\Big|\le\frac{Be^{-\varepsilon u/2}}{m}.$$
--
--   Role: bounds the horizontal pieces joining the shifted vertex to the rays from $p_c$ in part (i). Notation as in the paper: $f=f_{\gamma,q}$ is the phase function, $p_c$ the double critical point, $\nu=\nu(\gamma)$, $g$ the spike factor $\prod_{j>k}(\pi_j-z)$-type product of (103), $Z_M$ the normalisation (116), and $\mathcal H$-integrand $h_H(z)=e^{-\sigma u(z-q)}e^{Mf(z)}(p_c-z)^{-k}g(z)^{-1}$, $\sigma=\nu M^{1/3}$; $\mathcal J$-integrand $h_J(z)=e^{\sigma v(z-q)}e^{-Mf(z)}(p_c-z)^{k}g(z)$.
-- source:
--   J. Baik, G. Ben Arous and S. Peche, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), https://doi.org/10.1214/009117905000000233, the local analysis near $p_c$, proof of Proposition 3.1, pp. 1661-1664

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open Complex MeasureTheory

namespace SpikedWishart.SoftEdge

theorem H_conn_piece :
    ∀ (ε U₀ C₁ K₂ δ₀ δ θ : ℝ) (k : ℕ), 0 < ε → Real.cos θ = 1 / 2 →
    Real.sin θ ^ 2 = 3 / 4 → 0 ≤ C₁ → 0 ≤ K₂ → 0 < δ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {r : ℕ} (π : Fin r → ℝ) (γ q u m σ : ℝ) (M : ℕ),
      U₀ ≤ u → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ nu γ → nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ →
      σ = nu γ * m → q = pc γ - ε / σ → δ + ε / (2 * σ) ≤ δ₀ →
      (C₁ + K₂) * (nu γ * δ + ε / (2 * m)) ≤ 1 / 8 → 1 ≤ σ * δ →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → ‖fFn γ q z - fFn γ q (pc γ) -
          ((nu γ ^ 3 / 3 : ℝ) : ℂ) * (z - pc γ) ^ 3‖ ≤ C₁ * ‖z - pc γ‖ ^ 4) →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → gFn k π z ≠ 0 ∧
          ‖gFn k π (pc γ) / gFn k π z - 1‖ ≤ K₂ * ‖z - pc γ‖) →
      ‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ s in (0 : ℝ)..(pc γ - (pc γ + (-ε / 2) / σ)), (fun z : ℂ => exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * (z - q)) * exp ((M : ℂ) * fFn γ q z) * (1 / (((pc γ : ℂ) - z) ^ k * gFn k π z)))
            (((pc γ + (-ε / 2) / σ : ℝ) : ℂ) + (δ : ℂ) * exp ((θ : ℂ) * I) + (s : ℂ))‖ ≤
        B * Real.exp (-(ε / 2) * u) / m := by sorry

end SpikedWishart.SoftEdge
