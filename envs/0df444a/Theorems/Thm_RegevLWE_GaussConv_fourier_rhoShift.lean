-- Prove2me | Theorems.Thm_RegevLWE_GaussConv_fourier_rhoShift
-- name    : RegevLWE.GaussConv.fourier_rhoShift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:08:28.502741+00:00
-- url     : https://prove2.me/theorems/9cd72253-d36d-49a2-bb5c-60ac33fe086c
-- title:
--   Proof of Claim 3.9, p. 34:25 — Fourier transform of a shifted Gaussian: ρ̂_{σ,c}(w) = exp(−2πi⟨c, w⟩)·σⁿρ_{1/σ}(w)
-- statement:
--   Let $\sigma > 0$ and $c, w \in \mathbb{R}^n$. With the Fourier transform $\hat h(w) = \int_{\mathbb{R}^n} h(x) e^{-2\pi i \langle x, w\rangle}\,dx$ (p. 34:20), the shifted Gaussian $\rho_{\sigma,c}(x) = \rho_\sigma(x - c)$ satisfies
--   $$\widehat{\rho_{\sigma,c}}(w) = \exp\bigl(-2\pi i \langle c, w\rangle\bigr)\cdot \sigma^n \rho_{1/\sigma}(w).$$
--
--   This combines Eq. (9) with $\widehat{\rho_s} = s^n \rho_{1/s}$ (p. 34:20). The two transforms written out in the proof of Claim 3.9 (p. 34:25) are its instances $\sigma = rs/t$, $c = (r/t)^2 x - u$ and $\sigma = r$, $c = -u$; the transform in the proof of Claim 3.8 (p. 34:24) is the instance $\sigma = r$, $c = -c$.
--
--   **Formalization Note** $\hat h$ is Mathlib's `𝓕` on `EuclideanSpace ℝ (Fin n)`, i.e. $\int e^{-2\pi i\langle x, w\rangle} h(x)\,dx$ with Lebesgue measure, the paper's normalization. The Gaussian is coerced to a complex-valued function.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:25, display after 'Using Eq. (9),' in the proof of Claim 3.9; p. 34:20, Eq. (9) and ρ̂_s = sⁿρ_{1/s}

import Mathlib
import Definitions.Def_RegevLWE_GaussConv_Gaussian
import Definitions.Def_RegevLWE_GaussConv_Lattice

open FourierTransform

namespace RegevLWE.GaussConv

theorem fourier_rhoShift {n : ℕ} {σ : ℝ} (hσ : 0 < σ) (c w : EuclideanSpace ℝ (Fin n)) :
    𝓕 (fun x : EuclideanSpace ℝ (Fin n) => (rhoShift σ c x : ℂ)) w =
      Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ c w : ℝ))) * (σ : ℂ) ^ n *
        (rho (1 / σ) w : ℂ) := by sorry

end RegevLWE.GaussConv
