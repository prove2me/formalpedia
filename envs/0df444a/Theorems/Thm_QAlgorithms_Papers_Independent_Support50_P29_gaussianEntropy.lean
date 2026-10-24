-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P29_gaussianEntropy
-- name    : QAlgorithms.Papers.Independent.Support50.P29.gaussianEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:14:32.59964+00:00
-- url     : https://prove2.me/theorems/acb793e6-0fe8-4aab-b1af-72adec996b87
-- title:
--   General Gaussian spectral entropy, equation (2.6)
-- statement:
--   Let $s\ge1$, $\hbar>0$, and $\Delta=\hbar\begin{bmatrix}0&I\\-I&0\end{bmatrix}$ in grouped $(q;p)$ coordinates. On a nonzero complete separable complex Hilbert space carrying a regular irreducible Weyl representation, let $\rho$ be a normalized centered Gaussian state with real symmetric covariance $\alpha$, characteristic $\exp(-z^T\alpha z/2)$, and $\alpha-i\Delta/2\ge0$. Then $A=\Delta^{-1}\alpha$ is diagonalizable over $\mathbb C$ with eigenvalues $\pm ia_j$, $a_j\ge1/2$, counting multiplicities. Moreover,
--   $$
--   H(\rho)=\frac12\operatorname{Sp}\,g\!\left(\operatorname{abs}(A)-\frac I2\right)<\infty.
--   $$
--   Here $g(x)=(x+1)\log(x+1)-x\log x$, continuously extended at zero. For $A=P\operatorname{diag}(\lambda_j)P^{-1}$, the matrix on the right is $P\operatorname{diag}(g(|\lambda_j|-1/2))P^{-1}$. This is similarity spectral calculus, including pure modes; it is not the singular-value absolute value. The formula identifies actual state entropy from a finite covariance matrix.
-- source:
--   Sending Quantum Information with Gaussian States, arXiv:quant-ph/9809022v1, PDF p. 6, §2, equation (2.6): entropy of a general Gaussian state

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P29

noncomputable section

open Filter

open scoped BigOperators ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support50.P29

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma complexify)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity rankOne productCoeff tensorApply IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

open QAlgorithms.Papers.Independent.Frontier30.P10 (WeylSystem)

open QAlgorithms.Papers.Independent.Frontier30.P14 (partialRight PureDensity)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (tracePair thermalInput thermalPurificationDensity vacuumChannel exchangeMatrix RealizedDensity)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

/-- Holevo quant-ph/9809022v1, PDF pp.5-6, (2.6): paired imaginary
spectrum, diagonalizability, and actual finite entropy. The matrix function
is similarity calculus; replacing it by the singular-value absolute value
would change the formula for a squeezed covariance. Pure modes are allowed. -/
theorem gaussianEntropy {I : Type} [Countable I] [Nonempty I]
    (s : ℕ) (hs : 0 < s) (hbar : ℝ) (hhbar : 0 < hbar)
    (W : WeylSystem (Hilbert I) s) (rho : State I)
    (alpha : Matrix (Phase s) (Phase s) ℝ) (hrho : CenteredGaussianWithCovariance hbar W rho alpha) :
    (∃ (P : Matrix (Phase s) (Phase s) ℂ) (a : Fin s → ℝ),
      (∀ j, 1 / 2 ≤ a j) ∧
      SimilarityData (complexify ((canonicalCommutation s hbar)⁻¹ * alpha)) P
        (Sum.elim (fun j => Complex.I * (a j : ℂ))
          (fun j => -Complex.I * (a j : ℂ)))) ∧
    extendedEntropyNats rho.coefficients = ENNReal.ofReal
      ((entropyMatrix (complexify ((canonicalCommutation s hbar)⁻¹ * alpha))).trace.re / 2) := by sorry

end QAlgorithms.Papers.Independent.Support50.P29

end
