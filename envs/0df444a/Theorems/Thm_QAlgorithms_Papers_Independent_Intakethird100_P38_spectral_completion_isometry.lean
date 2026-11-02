-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P38_spectral_completion_isometry
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P38.spectral_completion_isometry
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:26:05.16991+00:00
-- url     : https://prove2.me/theorems/cce43298-4384-4bd1-a9b7-5241eef82454
-- title:
--   The separated spectral completion and the specified factor
-- statement:
--   Let $n\ge1$, let $\mathcal S=\mathcal S(\mathbb R^n;\mathbb C)$ have its full Schwartz Fréchet topology, and write $\widehat\psi(u)=\int_{\mathbb R^n}e^{-iu\cdot x}\psi(x)\,dx$. Let $\mathcal C$ consist of the regular positive Borel measures $\sigma$ for which $\int(1+|u|^2)^{-p}\,d\sigma(u)<\infty$ for some nonnegative integer $p$.
--
--   Suppose $\sigma\in\mathcal C$, $L^2(\sigma)$ is infinite dimensional, and fix a complex Hilbert isometric isomorphism $W:L^2(\sigma)\to L^2(dx)$. Let $H_\sigma$ be the separated completion of $\mathcal S$ for the seminorm $(\int|\widehat\psi|^2\,d\sigma)^{1/2}$, concretely the closure of its Fourier image in $L^2(\sigma)$. There exists an isometric isomorphism $E:H_\sigma\to L^2(dx)$ with
--
--   $$E[\psi]=W[\widehat\psi]_\sigma\qquad(\psi\in\mathcal S).$$
--
--   Thus the identification is the extension of the constructed $Q$, rather than equality of types or an arbitrary Hilbert-space isomorphism.
-- source:
--   Stochastic processes induced by singular operators, arXiv:1109.5273v1, PDF p. 10, Corollary 3.6: completion via Qσ

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P38

open MeasureTheory Filter

open scoped Topology ComplexConjugate ENNReal

/-- Corollary 3.6, PDF pp.10--11: the separated spectral completion is isometrically
onto L2(dx), by the specific extension of Q=W composed with Fourier inclusion. -/
theorem spectral_completion_isometry (n : ℕ) (hn : 0 < n)
    (σ : Measure (SpectralDomain n)) (hσ : InC σ) (hinfinite : ¬ FiniteDimensional ℂ (L2 σ))
    (W : L2 σ ≃ₗᵢ[ℂ] L2 (volume : Measure (SpectralDomain n))) :
    (∀ ψ : ComplexTest n, MemLp (paperFourier ψ) 2 σ) ∧
    ∃ E : spectralCompletion σ ≃ₗᵢ[ℂ] L2 (volume : Measure (SpectralDomain n)),
      ∀ ψ : ComplexTest n, E (spectralVector σ ψ) = factorFromW W ψ := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P38

end
