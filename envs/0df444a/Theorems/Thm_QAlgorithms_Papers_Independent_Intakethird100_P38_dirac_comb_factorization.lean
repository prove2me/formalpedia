-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P38_dirac_comb_factorization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P38.dirac_comb_factorization
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:30:48.849454+00:00
-- url     : https://prove2.me/theorems/a29884f4-867e-4f51-9152-0d72b601b526
-- title:
--   Dirac comb factorization and corrected periodization
-- statement:
--   Let $\mathcal S=\mathcal S(\mathbb R;\mathbb C)$ have its full Fréchet topology, put $\widehat\psi(u)=\int e^{-iux}\psi(x)\,dx$, and let $\sigma=\sum_{m\in\mathbb Z}\delta_m$. Fix a complex Hilbert isometric isomorphism $W:\ell^2(\mathbb Z)\to L^2(\mathbb R,dx)$. The Fourier samples are square summable, $Q\psi=W((\widehat\psi(m))_m)$ is continuous complex-linear, and
--
--   $$\|Q\psi\|_2^2=\sum_{m\in\mathbb Z}|\widehat\psi(m)|^2=\int|\widehat\psi|^2\,d\sigma.$$
--
--   The adjoint product is continuous into the distribution anti-dual and satisfies, for all $\psi,\varphi\in\mathcal S$,
--
--   $$\langle Q^*Q\psi,\varphi\rangle=2\pi\int_{\mathbb R}\left(\sum_{m\in\mathbb Z}\psi(x+2\pi m)\right)\overline{\varphi(x)}\,dx.$$
--
--   The series converges absolutely at every $x$, and the displayed integral is integrable. The factor $2\pi$ corrects (12.2) under the paper's stated Fourier convention; it is a disclosed source correction.
-- source:
--   Stochastic processes induced by singular operators, arXiv:1109.5273v1, PDF p. 26, Proposition 12.1: Dirac comb factorization and periodization

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P38

open MeasureTheory Filter

open scoped Topology ComplexConjugate ENNReal

/-- Proposition 12.1, PDF pp.26--27. SOURCE CORRECTION: under the paper's
unnormalized Fourier convention, (12.2) must read Q*Q=2π times periodization.
The printed W must be isometric, as (12.1) and its proof require. All continuity
is Schwartz Fréchet continuity; no Lebesgue-L2 boundedness is asserted.
The anti-dual formulation is the distributional equality, not pointwise evaluation. -/
theorem dirac_comb_factorization
    (W : SequenceL2 ≃ₗᵢ[ℂ] L2 (volume : Measure (SpectralDomain 1))) :
    ∃ Q : ComplexTest 1 →L[ℂ] L2 (volume : Measure (SpectralDomain 1)),
      ∃ A : ComplexTest 1 →L[ℂ] AntiDual 1,
        (∀ ψ, Q ψ = W (l2Class Measure.count (combSamples ψ))) ∧
        (∀ ψ, MemLp (combSamples ψ) 2 Measure.count ∧
          fourierEnergy diracComb ψ = ENNReal.ofReal (‖Q ψ‖ ^ 2) ∧
          ∀ x, Summable (fun m : ℤ => ψ (x + point1 (2 * Real.pi * (m : ℝ))))) ∧
        (∀ ψ, A ψ = adjointProduct Q ψ ∧ ∀ φ : ComplexTest 1,
          Integrable (fun x => periodization ψ x * conj (φ x)) volume ∧
          A ψ φ = (2 * Real.pi : ℂ) *
            ∫ x, periodization ψ x * conj (φ x)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P38

end
