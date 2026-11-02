-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P38_distributional_adjoint_product
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P38.distributional_adjoint_product
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:27:49.174204+00:00
-- url     : https://prove2.me/theorems/89a4be0a-851a-4ef6-91d2-0c2b9a5db259
-- title:
--   The distributional adjoint product is the spectral kernel
-- statement:
--   Let $n\ge1$, let $\mathcal S=\mathcal S(\mathbb R^n;\mathbb C)$ have its full Schwartz Fréchet topology, and write $\widehat\psi(u)=\int_{\mathbb R^n}e^{-iu\cdot x}\psi(x)\,dx$. Let $\mathcal C$ consist of the regular positive Borel measures $\sigma$ for which $\int(1+|u|^2)^{-p}\,d\sigma(u)<\infty$ for some nonnegative integer $p$.
--
--   Let $\sigma\in\mathcal C$ and let $Q:\mathcal S\to L^2(dx)$ be a continuous complex Hilbert factor of the spectral form (3.6). The spectral pairing defines a continuous complex-linear map $A$ into the continuous anti-dual of $\mathcal S$, and
--
--   $$ (A\psi)(\varphi)=\int\widehat\psi(u)\overline{\widehat\varphi(u)}\,d\sigma(u)=\langle Q\psi,Q\varphi\rangle_{\mathrm{source}},\qquad A=Q^*Q.$$
--
--   Here an anti-dual pairs against conjugated test functions; this is the distributional kernel $\widehat\sigma(t-s)$ in the proof's variable order. The final extra $du$ in the printed formula is removed. No real Gaussian assumption enters.
-- source:
--   Stochastic processes induced by singular operators, arXiv:1109.5273v1, PDF p. 14, Theorem 5.3: distributional adjoint product

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P38

open MeasureTheory Filter

open scoped Topology ComplexConjugate ENNReal

/-- Theorem 5.3, PDF pp.14--15. SOURCE CORRECTION: remove the duplicated final du
from (5.4). Use the proof's spectral pairing/kernel σ-hat(t-s), not pointwise
values of a distribution. The anti-dual pairs against conjugated test functions;
Mathlib inner(Q φ,Q ψ) is the source's first-slot-linear inner(Q ψ,Q φ).
No real Gaussian compatibility is assumed. -/
theorem distributional_adjoint_product (n : ℕ) (hn : 0 < n)
    (σ : Measure (SpectralDomain n)) (hσ : InC σ)
    (Q : ComplexTest n →L[ℂ] L2 (volume : Measure (SpectralDomain n))) (hQ : HilbertFactor σ Q) :
    ∃ A : ComplexTest n →L[ℂ] AntiDual n,
      (∀ ψ, A ψ = spectralDistribution σ ψ) ∧
      (∀ ψ φ, A ψ φ = spectralPairing σ ψ φ) ∧
      (∀ ψ, A ψ = adjointProduct Q ψ) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P38

end
