-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_mappingProducts
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.mappingProducts
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:59:20.608467+00:00
-- url     : https://prove2.me/theorems/ee7535d7-ee3b-4bd9-992a-2004a628b161
-- title:
--   Unnumbered normalization and product preservation
-- statement:
--   For the spectral-pair map $p_{ij}=\lambda_i|\langle x_i,y_j\rangle|^2$, $q_{ij}=\mu_j|\langle x_i,y_j\rangle|^2$, both $p$ and $q$ are normalized probability laws. Their tensor products are orthonormal eigenbases of the tensor-copy states, and preserve the map:
--
--   $$p^{(n)}_{\mathbf i,\mathbf j}=\prod_{k=1}^n p_{i_kj_k},\qquad q^{(n)}_{\mathbf i,\mathbf j}=\prod_{k=1}^n q_{i_kj_k}.$$
--
--   Here $p^{(n)},q^{(n)}$ are obtained from the product eigenvalues and the overlaps of the product eigenvectors. The empty tensor power is included and gives the singleton law.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 10, Unnumbered normalization and product preservation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P45

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P45

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal BigOperators Topology

open QAlgorithms.Papers.Independent.Information100.P07
  (support positivePart positiveProjection IsProjection)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (logNonnegativeExtended relativeEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P15 (positiveMatrixRpow)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:0708.4282v1, PDF p.10: Unnumbered normalization and product preservation. -/
theorem mappingProducts (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (D : SpectralPair rho sigma) :
    IsLaw (spectralP D) ∧ IsLaw (spectralQ D) ∧
    (∀ n : ℕ,
      (copies n (D.leftBasis : Mat I))ᴴ * copies n (D.leftBasis : Mat I) = 1 ∧
      copies n (D.leftBasis : Mat I) * (copies n (D.leftBasis : Mat I))ᴴ = 1 ∧
      (copies n (D.rightBasis : Mat I))ᴴ * copies n (D.rightBasis : Mat I) = 1 ∧
      copies n (D.rightBasis : Mat I) * (copies n (D.rightBasis : Mat I))ᴴ = 1 ∧
      copies n rho = copies n (D.leftBasis : Mat I) *
        Matrix.diagonal (fun x => ((∏ k, D.leftValues (x k) : ℝ) : ℂ)) *
          (copies n (D.leftBasis : Mat I))ᴴ ∧
      copies n sigma = copies n (D.rightBasis : Mat I) *
        Matrix.diagonal (fun x => ((∏ k, D.rightValues (x k) : ℝ) : ℂ)) *
          (copies n (D.rightBasis : Mat I))ᴴ) ∧
    (∀ n : ℕ, ∀ x y : Fin n → I,
      (∏ k, D.leftValues (x k)) *
        Complex.normSq (∑ z : Fin n → I,
          star (∏ k, (D.leftBasis : Mat I) (z k) (x k)) *
            (∏ k, (D.rightBasis : Mat I) (z k) (y k))) =
          ∏ k, spectralP D (x k,y k)) ∧
    (∀ n : ℕ, ∀ x y : Fin n → I,
      (∏ k, D.rightValues (y k)) *
        Complex.normSq (∑ z : Fin n → I,
          star (∏ k, (D.leftBasis : Mat I) (z k) (x k)) *
            (∏ k, (D.rightBasis : Mat I) (z k) (y k))) =
          ∏ k, spectralQ D (x k,y k)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
