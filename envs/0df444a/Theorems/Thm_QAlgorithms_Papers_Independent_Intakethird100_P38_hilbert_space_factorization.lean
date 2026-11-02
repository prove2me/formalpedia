-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P38_hilbert_space_factorization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P38.hilbert_space_factorization
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:24:44.402306+00:00
-- url     : https://prove2.me/theorems/25c212eb-7617-4b7e-a119-06d90da82c59
-- title:
--   Continuous Hilbert factorization of the spectral form
-- statement:
--   Let $n\ge1$, let $\mathcal S=\mathcal S(\mathbb R^n;\mathbb C)$ have its full Schwartz Fréchet topology, and write $\widehat\psi(u)=\int_{\mathbb R^n}e^{-iu\cdot x}\psi(x)\,dx$. Let $\mathcal C$ consist of the regular positive Borel measures $\sigma$ for which $\int(1+|u|^2)^{-p}\,d\sigma(u)<\infty$ for some nonnegative integer $p$.
--
--   Suppose $\sigma\in\mathcal C$ and the complex Hilbert space $L^2(\sigma)$ is infinite dimensional. There exists a continuous complex-linear map $Q:\mathcal S\to L^2(\mathbb R^n,dx)$ such that
--
--   $$\langle Q\psi,Q\varphi\rangle_{\mathrm{source}}=\int\widehat\psi(u)\overline{\widehat\varphi(u)}\,d\sigma(u),\qquad\|Q\psi\|_2^2=\int|\widehat\psi|^2\,d\sigma.$$
--
--   This realizes the spectral form in Lebesgue $L^2$. The codomain follows the construction and proof, correcting the printed $L^2(\sigma)$. Mathlib's conjugate-linear-first inner product reverses the displayed slots.
-- source:
--   Stochastic processes induced by singular operators, arXiv:1109.5273v1, PDF p. 9, Theorem 3.4: Hilbert-space factorization

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P38

open MeasureTheory Filter

open scoped Topology ComplexConjugate ENNReal

/-- Theorem 3.4, PDF pp.9--10. SOURCE CORRECTION: the theorem and (3.6) print
L2(σ); (3.7), §1(b), and every norm in the proof use L2(dx), used here.
The explicit infinite-dimensional assumption is retained. -/
theorem hilbert_space_factorization (n : ℕ) (hn : 0 < n)
    (σ : Measure (SpectralDomain n)) (hσ : InC σ) (hinfinite : ¬ FiniteDimensional ℂ (L2 σ)) :
    ∃ Q : ComplexTest n →L[ℂ] L2 (volume : Measure (SpectralDomain n)),
      HilbertFactor σ Q ∧ ∀ ψ : ComplexTest n,
        fourierEnergy σ ψ = ENNReal.ofReal (‖Q ψ‖ ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P38

end
