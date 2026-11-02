-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P38_fourier_onto_covariance_rkhs
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P38.fourier_onto_covariance_rkhs
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:28:22.502674+00:00
-- url     : https://prove2.me/theorems/6d87a43c-7981-4f8a-9248-188313eccced
-- title:
--   Fourier transform onto the full covariance RKHS
-- statement:
--   Let $n\ge1$, let $\mathcal S=\mathcal S(\mathbb R^n;\mathbb C)$ have its full Schwartz Fréchet topology, and write $\widehat\psi(u)=\int_{\mathbb R^n}e^{-iu\cdot x}\psi(x)\,dx$. Let $\mathcal C$ consist of the regular positive Borel measures $\sigma$ for which $\int(1+|u|^2)^{-p}\,d\sigma(u)<\infty$ for some nonnegative integer $p$.
--
--   For $\sigma\in\mathcal C$, there exists a probability law $\mu$ on the continuous real tempered dual satisfying $\int e^{i\omega(\psi)}\,d\mu=\exp(-\frac12\int|\widehat\psi|^2\,d\sigma)$ for every real test. Define $C_\sigma(\psi,\varphi)=\exp(-\frac12\int|\widehat{\psi-\varphi}|^2\,d\sigma)$. This kernel is positive semidefinite, and the transform
--
--   $$ (F_\sigma f)(\psi)=\int_\Omega e^{-i\omega(\psi)}f(\omega)\,d\mu(\omega) $$
--
--   is a complex-linear isometric isomorphism from the full $L^2(\mu)$ onto the complex reproducing kernel Hilbert space $H(C_\sigma)$, with real Schwartz indices $\psi$. Constants and every Gaussian chaos are included.
-- source:
--   Stochastic processes induced by singular operators, arXiv:1109.5273v1, PDF p. 15, Theorem 6.1: Fourier transform onto the covariance RKHS

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P38

open MeasureTheory Filter

open scoped Topology ComplexConjugate ENNReal

/-- Theorem 6.1, PDF pp.15--17: the full Fourier transform, including constants
and all chaoses, is isometric ONTO the covariance RKHS. Kernel positivity and the
probability law are conclusions; RKHS.OfKernel supplies the separated completion. -/
theorem fourier_onto_covariance_rkhs (n : ℕ) (hn : 0 < n)
    (σ : Measure (SpectralDomain n)) (hσ : InC σ) :
    ∃ μ : Measure (Omega n), CharacteristicLaw σ μ ∧
      ∃ hK : (covarianceKernel σ).PosSemidef,
        letI : Fact (covarianceKernel σ).PosSemidef := ⟨hK⟩
        ∃ E : MeasureTheory.Lp ℂ 2 μ ≃ₗᵢ[ℂ] RKHS.OfKernel (covarianceKernel σ),
          ∀ (f : MeasureTheory.Lp ℂ 2 μ) (ψ : RealTest n),
            (E f) ψ = lawFourier μ f ψ := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P38

end
