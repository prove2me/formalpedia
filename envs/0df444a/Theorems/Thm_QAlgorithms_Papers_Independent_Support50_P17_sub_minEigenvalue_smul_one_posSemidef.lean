-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P17_sub_minEigenvalue_smul_one_posSemidef
-- name    : QAlgorithms.Papers.Independent.Support50.P17.sub_minEigenvalue_smul_one_posSemidef
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-29T18:22:11.79067+00:00
-- url     : https://prove2.me/theorems/831a4ab2-2146-4c00-a64e-67ede7f73832
-- title:
--   A Hermitian matrix dominates its smallest eigenvalue times the identity
-- statement:
--   Let $A$ be a Hermitian matrix on a finite index set and let $\lambda_{\min}(A)$ be its smallest eigenvalue. Then
--
--   $$
--   A-\lambda_{\min}(A)\,I\succeq0 .
--   $$
--
--   This is the Rayleigh-quotient characterisation of the smallest eigenvalue, used to convert the hypothesis $\lambda_{\min}(\sigma)=\beta$ into the operator inequality $\sigma\ge\beta I$.
--
--   **Formalization Note** $\lambda_{\min}$ is the frozen `minEigenvalue` (the first entry of the ascending eigenvalue list); on the empty index type the statement is trivial.
-- source:
--   Horn--Johnson, Matrix Analysis (2nd ed.), Theorem 4.2.2 (Rayleigh--Ritz); used in Audenaert--Eisert, Continuity bounds on the quantum relative entropy - II, arXiv:1105.2656v3, proof of Corollary 1 (PDF p. 9), via sigma >= beta I

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

namespace QAlgorithms.Papers.Independent.Support50.P17

attribute [local instance] Classical.propDecidable Classical.decEq

theorem sub_minEigenvalue_smul_one_posSemidef {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    (A - ((minEigenvalue A : ℝ) : ℂ) • (1 : Matrix I I ℂ)).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Support50.P17

end
