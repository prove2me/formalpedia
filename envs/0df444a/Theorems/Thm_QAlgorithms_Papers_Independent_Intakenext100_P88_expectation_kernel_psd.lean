-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P88_expectation_kernel_psd
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P88.expectation_kernel_psd
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T08:24:30.012811+00:00
-- url     : https://prove2.me/theorems/e69bf2b6-9244-4526-bcae-860255c5620d
-- title:
--   Expectation-value QNTK is symmetric and positive semidefinite
-- statement:
--   The circuit acts on a nonzero finite-dimensional complex Hilbert space $H=\mathbb C^h$ and has the ordered form $U(\theta)=\prod_{\ell=1}^L W_\ell\exp(i\theta_\ell X_\ell)$, with fixed unitary $W_\ell$, Hermitian $X_\ell$, and real angles. Products are written in increasing index order and the rightmost factor acts first. Feature vectors $\phi(x)$ have norm one. For Hermitian observables $O_i$, put $z_{x,i}(\theta)=\langle U(\theta)\phi(x),O_iU(\theta)\phi(x)\rangle\in\mathbb R$.
--
--   For arbitrary angles define $K_{ab}=\sum_\ell\partial_{\theta_\ell}z_a\,\partial_{\theta_\ell}z_b$, where $a,b$ range over data-observable pairs. Then
--   $$
--   K_{ab}=K_{ba},\qquad [K_{a_p a_q}]_{p,q=1}^n\succeq0
--   $$
--   for every finite list $a_1,\ldots,a_n$, including an empty list. Thus an infinite data space is handled through its finite Gram submatrices. No entrywise positivity or nonsingularity is claimed. This supplies a positive semidefinite kernel for the expectation model.
-- source:
--   Representation Learning via Quantum Neural Tangent Kernels, arXiv:2111.04225v3, PDF p. 24, SM Theorem 1; Eq.(94)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P88

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

/-- PDF p.24 SM Theorem 1, Eq.(94): symmetry and PSD for every finite Gram submatrix.
No finite-dimensional operator on an infinite data space is postulated. -/
theorem expectation_kernel_psd {D I : Type*} [Fintype I] {h L : ℕ}
    (M : ExpectationNetwork D I h L) (theta : Fin L → ℝ) :
    (∀ a b, expectationKernel M theta a b = expectationKernel M theta b a) ∧
    ∀ (n : ℕ) (a : Fin n → D × I),
      Matrix.PosSemidef (fun i j => expectationKernel M theta (a i) (a j)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P88

end
