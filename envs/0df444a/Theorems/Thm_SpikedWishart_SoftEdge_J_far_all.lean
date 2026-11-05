-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_J_far_all
-- name    : SpikedWishart.SoftEdge.J_far_all
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-04T06:28:40.590777+00:00
-- url     : https://prove2.me/theorems/e4a4ceae-f08c-4774-bb96-adcfc2620bbe
-- title:
--   Far from $p_c$ the pieces of the $\mathcal J$-contour are $O(e^{-\varepsilon v}/M^{1/3})$
-- statement:
--   For the parameters of the statement there is $B\ge0$ such that, if $\mathrm{Re}(-f)$ decreases along the far rays and horizontals of the $\Sigma$-contour, is largest at the corner, and has cubic decay at the start of the far ray, then each far piece $I$ of the rescaled $\mathcal J$-integral satisfies
--
--   $$\Big|\frac{\sigma}{2\pi Z_M}I\Big|\le\frac{Be^{-\varepsilon v}}{m}.$$
--
--   Role: the tail estimate of part (ii); the monotonicity hypotheses are supplied by Lemma 3.2. Notation as in the paper: $f=f_{\gamma,q}$ is the phase function, $p_c$ the double critical point, $\nu=\nu(\gamma)$, $g$ the spike factor $\prod_{j>k}(\pi_j-z)$-type product of (103), $Z_M$ the normalisation (116), and $\mathcal H$-integrand $h_H(z)=e^{-\sigma u(z-q)}e^{Mf(z)}(p_c-z)^{-k}g(z)^{-1}$, $\sigma=\nu M^{1/3}$; $\mathcal J$-integrand $h_J(z)=e^{\sigma v(z-q)}e^{-Mf(z)}(p_c-z)^{k}g(z)$.
-- source:
--   J. Baik, G. Ben Arous and S. Peche, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), https://doi.org/10.1214/009117905000000233, the estimates away from $p_c$ using Lemma 3.2, proof of Proposition 3.1, pp. 1661-1664

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open Complex MeasureTheory

namespace SpikedWishart.SoftEdge

theorem J_far_all :
    ∀ (ε V₀ γ₀ P₀ δ R Nmax d : ℝ) (r k : ℕ), 0 < ε → 1 ≤ γ₀ → 0 ≤ P₀ →
    0 < δ → δ ≤ 1 / (2 * (γ₀ + 1)) → 0 ≤ R → 0 ≤ Nmax → 0 < d → d ≤ P₀ + 1 →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (π : Fin r → ℝ) (γ q v m σ ℓ : ℝ) (M : ℕ),
      V₀ ≤ v → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ γ → γ ≤ γ₀ → 0 ≤ nu γ → nu γ ≤ Nmax →
      nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ → σ = nu γ * m → q = pc γ - ε / σ → 4 * ε ≤ σ * δ →
      (∀ j : Fin r, k ≤ (j : ℕ) → 0 ≤ π j ∧ π j ≤ P₀) →
      (∀ j : Fin r, k ≤ (j : ℕ) → d ≤ ‖(π j : ℂ) - pc γ‖) → ℓ = 2 * pc γ →
      3 * ε / (nu γ * (M : ℝ) ^ (1 / 3 : ℝ)) ≤ δ →
      StrictAntiOn (fun t : ℝ =>
        (-fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))).re)
        (Set.Icc (3 * ε / (nu γ * (M : ℝ) ^ (1 / 3 : ℝ))) (2 * pc γ)) →
      StrictAntiOn (fun x : ℝ =>
        (-fFn γ q ((pc γ : ℂ) + 2 * (pc γ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) -
          (x : ℂ))).re) (Set.Icc 0 R) →
      (∀ y : ℝ, 0 ≤ y → y ≤ Real.sqrt 3 * pc γ →
        (-fFn γ q (-(R : ℂ) + ((Real.sqrt 3 * pc γ - y : ℝ) : ℂ) * I)).re ≤
          (-fFn γ q ((pc γ : ℂ) + 2 * (pc γ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))).re) →
      (-fFn γ q ((pc γ : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))).re -
        (-fFn γ q (pc γ)).re ≤ -(δ ^ 3 / 6) →
      (‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ y in (-(ℓ * (Real.sqrt 3 / 2)))..(ℓ * (Real.sqrt 3 / 2)),
            (exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * ((((pc γ - ℓ / 2 - R : ℝ) : ℂ) + (y : ℂ) * I) - q)) * exp (-(M : ℂ) * fFn γ q (((pc γ - ℓ / 2 - R : ℝ) : ℂ) + (y : ℂ) * I)) * (((pc γ : ℂ) - (((pc γ - ℓ / 2 - R : ℝ) : ℂ) + (y : ℂ) * I)) ^ k * gFn k π (((pc γ - ℓ / 2 - R : ℝ) : ℂ) + (y : ℂ) * I))) * I‖ ≤
          B * Real.exp (-ε * v) / m) ∧
      (‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ x in (0 : ℝ)..R, (fun z : ℂ => exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (z - q)) * exp (-(M : ℂ) * fFn γ q z) * (((pc γ : ℂ) - z) ^ k * gFn k π z))
            ((pc γ : ℂ) + (ℓ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) - (x : ℂ))‖ ≤
          B * Real.exp (-ε * v) / m) ∧
      (‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in δ..ℓ, (exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (((pc γ : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) - q)) * exp (-(M : ℂ) * fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))) * (((pc γ : ℂ) - ((pc γ : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))) ^ k * gFn k π ((pc γ : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)))) *
            exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)‖ ≤
          B * Real.exp (-ε * v) / m) ∧
      (‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in δ..ℓ, (exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (((pc γ : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)) - q)) * exp (-(M : ℂ) * fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I))) * (((pc γ : ℂ) - ((pc γ : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I))) ^ k * gFn k π ((pc γ : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)))) *
            exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)‖ ≤
          B * Real.exp (-ε * v) / m) ∧
      (‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ x in (0 : ℝ)..R, (fun z : ℂ => exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (z - q)) * exp (-(M : ℂ) * fFn γ q z) * (((pc γ : ℂ) - z) ^ k * gFn k π z))
            ((pc γ : ℂ) + (ℓ : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) - (x : ℂ))‖ ≤
          B * Real.exp (-ε * v) / m) := by sorry

end SpikedWishart.SoftEdge
