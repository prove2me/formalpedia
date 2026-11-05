-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_H_far_all
-- name    : SpikedWishart.SoftEdge.H_far_all
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-04T07:54:31.349139+00:00
-- url     : https://prove2.me/theorems/c249099e-2ad6-4bcf-b57b-2127472cb493
-- title:
--   Far from $p_c$ the five pieces of the $\mathcal H$-contour are $O(e^{-\varepsilon u/2}/M^{1/3})$
-- statement:
--   Let $\varepsilon>0$, $\gamma_0\ge1$, $0\le P_0\le R$, $1\le R$, $0<\delta\le1/(2(\gamma_0+1))$, $N_{\max}\ge0$. There is $B\ge0$ such that for $1\le\gamma\le\gamma_0$, $0\le\nu\le N_{\max}$, spikes $0\le\pi_j\le P_0$, $\ell=2(1-p_c)$, $\sigma\delta\ge1$, if $\mathrm{Re}f$ decreases along $p_c+t\omega$ ($\delta\le t\le\ell$) and along $p_c+\ell\omega+x$ ($0\le x\le R$), is largest at the corner on the vertical side, and $\mathrm{Re}f(p_c+\delta\omega)-\mathrm{Re}f(p_c)\le-\delta^3/6$, then each of the five far pieces $I$ (vertical side, the two horizontals, the two rays beyond $\delta$) satisfies
--
--   $$\Big|Z_M\frac{\sigma}{2\pi}I\Big|\le\frac{Be^{-\varepsilon u/2}}{m}.$$
--
--   Role: the tail estimate of part (i); the monotonicity hypotheses are supplied by Lemma 3.1. Notation as in the paper: $f=f_{\gamma,q}$ is the phase function, $p_c$ the double critical point, $\nu=\nu(\gamma)$, $g$ the spike factor $\prod_{j>k}(\pi_j-z)$-type product of (103), $Z_M$ the normalisation (116), and $\mathcal H$-integrand $h_H(z)=e^{-\sigma u(z-q)}e^{Mf(z)}(p_c-z)^{-k}g(z)^{-1}$, $\sigma=\nu M^{1/3}$; $\mathcal J$-integrand $h_J(z)=e^{\sigma v(z-q)}e^{-Mf(z)}(p_c-z)^{k}g(z)$.
-- source:
--   J. Baik, G. Ben Arous and S. Peche, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), https://doi.org/10.1214/009117905000000233, the estimates away from $p_c$ using Lemma 3.1, proof of Proposition 3.1, pp. 1661-1664

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open Complex MeasureTheory

namespace SpikedWishart.SoftEdge

theorem H_far_all :
    ∀ (ε U₀ γ₀ P₀ δ R Nmax : ℝ) (r k : ℕ), 0 < ε → 1 ≤ γ₀ → 0 ≤ P₀ →
    0 < δ → δ ≤ 1 / (2 * (γ₀ + 1)) → 1 ≤ R → P₀ ≤ R → 0 ≤ Nmax →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (π : Fin r → ℝ) (γ q u m σ ℓ : ℝ) (M : ℕ),
      U₀ ≤ u → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ γ → γ ≤ γ₀ → 0 ≤ nu γ → nu γ ≤ Nmax →
      nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ → σ = nu γ * m → q = pc γ - ε / σ → 1 ≤ σ * δ →
      (∀ j : Fin r, k ≤ (j : ℕ) → 0 ≤ π j ∧ π j ≤ P₀) → ℓ = 2 * (1 - pc γ) →
      AntitoneOn (fun t : ℝ => (fFn γ q ((pc γ : ℂ) + (t : ℂ) *
        exp (((Real.pi / 3 : ℝ) : ℂ) * I))).re) (Set.Icc δ ℓ) →
      AntitoneOn (fun x : ℝ => (fFn γ q ((pc γ : ℂ) + (ℓ : ℂ) *
        exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ))).re) (Set.Icc 0 R) →
      (∀ y : ℝ, 0 ≤ y → y ≤ ℓ * (Real.sqrt 3 / 2) →
        (fFn γ q (1 + (R : ℂ) + (y : ℂ) * I)).re ≤
          (fFn γ q ((pc γ : ℂ) + (ℓ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I))).re) →
      (fFn γ q ((pc γ : ℂ) + (δ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I))).re -
        (fFn γ q (pc γ)).re ≤ -(δ ^ 3 / 6) →
      (‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ y in (-(ℓ * (Real.sqrt 3 / 2)))..(ℓ * (Real.sqrt 3 / 2)),
            (exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * ((((pc γ + ℓ / 2 + R : ℝ) : ℂ) + (y : ℂ) * I) - q)) * exp ((M : ℂ) * fFn γ q (((pc γ + ℓ / 2 + R : ℝ) : ℂ) + (y : ℂ) * I)) * (1 / (((pc γ : ℂ) - (((pc γ + ℓ / 2 + R : ℝ) : ℂ) + (y : ℂ) * I)) ^ k * gFn k π (((pc γ + ℓ / 2 + R : ℝ) : ℂ) + (y : ℂ) * I)))) * I‖ ≤
          B * Real.exp (-(ε / 2) * u) / m) ∧
      (‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ x in (0 : ℝ)..R, (exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * (((pc γ : ℂ) + (ℓ : ℂ) *
            exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ)) - q)) * exp ((M : ℂ) * fFn γ q ((pc γ : ℂ) + (ℓ : ℂ) *
            exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ))) * (1 / (((pc γ : ℂ) - ((pc γ : ℂ) + (ℓ : ℂ) *
            exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ))) ^ k * gFn k π ((pc γ : ℂ) + (ℓ : ℂ) *
            exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ)))))‖ ≤
          B * Real.exp (-(ε / 2) * u) / m) ∧
      (‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in δ..ℓ, (exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * (((pc γ : ℂ) + (t : ℂ) *
            exp (((Real.pi / 3 : ℝ) : ℂ) * I)) - q)) * exp ((M : ℂ) * fFn γ q ((pc γ : ℂ) + (t : ℂ) *
            exp (((Real.pi / 3 : ℝ) : ℂ) * I))) * (1 / (((pc γ : ℂ) - ((pc γ : ℂ) + (t : ℂ) *
            exp (((Real.pi / 3 : ℝ) : ℂ) * I))) ^ k * gFn k π ((pc γ : ℂ) + (t : ℂ) *
            exp (((Real.pi / 3 : ℝ) : ℂ) * I))))) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)‖ ≤
          B * Real.exp (-(ε / 2) * u) / m) ∧
      (‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in δ..ℓ, (exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * (((pc γ : ℂ) + (t : ℂ) *
            exp (((-Real.pi / 3 : ℝ) : ℂ) * I)) - q)) * exp ((M : ℂ) * fFn γ q ((pc γ : ℂ) + (t : ℂ) *
            exp (((-Real.pi / 3 : ℝ) : ℂ) * I))) * (1 / (((pc γ : ℂ) - ((pc γ : ℂ) + (t : ℂ) *
            exp (((-Real.pi / 3 : ℝ) : ℂ) * I))) ^ k * gFn k π ((pc γ : ℂ) + (t : ℂ) *
            exp (((-Real.pi / 3 : ℝ) : ℂ) * I))))) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I)‖ ≤
          B * Real.exp (-(ε / 2) * u) / m) ∧
      (‖ZM γ q M k π * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ x in (0 : ℝ)..R, (exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * (((pc γ : ℂ) + (ℓ : ℂ) *
            exp (((-Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ)) - q)) * exp ((M : ℂ) * fFn γ q ((pc γ : ℂ) + (ℓ : ℂ) *
            exp (((-Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ))) * (1 / (((pc γ : ℂ) - ((pc γ : ℂ) + (ℓ : ℂ) *
            exp (((-Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ))) ^ k * gFn k π ((pc γ : ℂ) + (ℓ : ℂ) *
            exp (((-Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ)))))‖ ≤
          B * Real.exp (-(ε / 2) * u) / m) := by sorry

end SpikedWishart.SoftEdge
