-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_minimum_output_multiplicative
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.minimum_output_multiplicative
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:00:04.787765+00:00
-- url     : https://prove2.me/theorems/fbb0eb8e-8647-483d-a171-09c9c697223a
-- title:
--   Theorem 9: multiplicative minimal output eigenvalue for EB positive maps
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree.
--
--   Let $T:M_{d_1}\to M_{d_2}$ be entanglement breaking, meaning that $(\mathrm{id}_r\otimes T)(X)$ is separable positive for every finite ancilla and every PSD input $X$. Let $S:M_{d_3}\to M_{d_4}$ be CP. Define $\lambda_{\rm out}^{\min}(L)=\min_{\rho\ge0,\operatorname{tr}\rho=1}\lambda_{\min}(L(\rho))$, including zero eigenvalues. Then
--   $$\lambda_{\rm out}^{\min}(T\otimes S)=\lambda_{\rm out}^{\min}(T)\lambda_{\rm out}^{\min}(S).$$
--   All three minima are attained. Neither map is assumed trace preserving, and zero maps are allowed. This is the minimal-eigenvalue multiplicativity used by Lemma 3.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 24, Theorem 9: multiplicative minimal output eigenvalue for EB positive maps

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P37

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

-- Only the following exact definition bodies are reused from pinned accepted papers.

open QAlgorithms.Papers.Independent.Information100.P04 (gamma copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)

open QAlgorithms.Papers.Independent.Information100.P50 (maxEigenvalue)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

namespace QAlgorithms.Papers.Independent.Bridge50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Theorem 9, PDF pp.5,24: EB positive T and CP S, neither assumed trace-preserving.
Zero maps and zero eigenvalues are retained. Minimum attainment is explicit. -/
theorem minimum_output_multiplicative [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (T : MatrixMap A B) (S : MatrixMap C D) (hT : RectangularEBPositive T) (hS : Entanglement.IsCompletelyPositive S) :
    minimumOutputEigenvalue (tensorLinearMap T S) = minimumOutputEigenvalue T * minimumOutputEigenvalue S ∧
    IsLeast (outputEigenvalues T) (minimumOutputEigenvalue T) ∧
    IsLeast (outputEigenvalues S) (minimumOutputEigenvalue S) ∧
    IsLeast (outputEigenvalues (tensorLinearMap T S)) (minimumOutputEigenvalue (tensorLinearMap T S)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
