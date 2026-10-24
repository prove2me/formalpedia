-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P30_partialDerivative_mean_variance
-- name    : QAlgorithms.Papers.Independent.Support50.P30.partialDerivative_mean_variance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:19:30.109002+00:00
-- url     : https://prove2.me/theorems/e05295e4-d3e3-4764-b225-2c6a8057f749
-- title:
--   Theorem 1 (Variance of partial derivatives)
-- statement:
--   Let $n\ge2$ and fix an orthonormal Schur decomposition of the $n$-qubit space, independently of the data and parameters. Its sectors $\lambda=(n-m,m)$ have block dimension $d_\lambda=n-2m+1$ and multiplicity $m_\lambda=\binom nm-\binom n{m-1}$, with the predecessor zero at $m=0$. Let $U(\theta)$ be a fixed layered circuit with generators from Eq. (9), let $O$ belong to Eq. (10), and fix a differentiated layer $\mu$. For density matrices $\rho_i$ and arbitrary real coefficients $c_i$, put $\sigma=\sum_i c_i\rho_i$ and $\widehat L(\theta)=\sum_i c_i\operatorname{Tr}(U(\theta)\rho_iU(\theta)^\dagger O)$. Under a probability law on the parameters, assume the two halves $U_A,U_B$, with $U_B$ including layer $\mu$, have joint conjugation moments through order two equal to the product Haar moments over both halves and all sectors. Then
--
--   $$\mathbb E_\theta[\partial_\mu\widehat L]=0,\qquad
--   \operatorname{Var}_\theta(\partial_\mu\widehat L)=\sum_{\lambda:d_\lambda>1}\frac{2d_\lambda}{(d_\lambda^2-1)^2}\Delta(H_{\mu,\lambda})\Delta(O_\lambda)\Delta\!\left(\sum_{\nu=1}^{m_\lambda}\sigma_\lambda^\nu\right).$$
--
--   Here $B_\lambda^\nu=Q_\lambda^\nu B(Q_\lambda^\nu)^\dagger$ is an unnormalized compression in the fixed common coordinates, and $\Delta(B)=\operatorname{Tr}(B^2)-\operatorname{Tr}(B)^2/\dim B$. One-dimensional sectors contribute zero. This exact identity separates the circuit, measurement and dataset factors; it makes no inverse-polynomial lower-bound claim.
-- source:
--   Theoretical Guarantees for Permutation-Equivariant Quantum Neural Networks, arXiv:2210.09974v3, PDF p. 6, Theorem 1 (Variance of partial derivatives); seed paper result

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator NNReal ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P30

/-- PDF p.6, Theorem 1, Eq.(16), with proof assumptions on pp.14,23-26.
One-dimensional sectors have zero commutators and are omitted explicitly. -/
theorem partialDerivative_mean_variance {n L M : ℕ} (hn : 2 ≤ n)
    (S : SchurFrame n) (word : Fin L → Fin 3) (mu : Fin L)
    (O : QnnOperator n) (hO : O ∈ qnnMeasurementFamily n) (hHerm : O.IsHermitian)
    (rho : Fin M → QnnDensity n) (c : Fin M → ℝ)
    (P : Measure (Fin L → ℝ)) [IsProbabilityMeasure P]
    (hdesign : IndependentBlockTwoDesign S (fun j => qnnGenerator n (word j)) mu P) :
    (∫ theta, partialLoss (fun j => qnnGenerator n (word j)) mu c rho O theta ∂P) = 0 ∧
    variance P (partialLoss (fun j => qnnGenerator n (word j)) mu c rho O) =
      ∑ m : Sector n, if 1 < blockDim n m then
        (2 * (blockDim n m : ℝ) / (((blockDim n m : ℝ) ^ 2 - 1) ^ 2)) *
          centeredDelta (commonBlock S m (qnnGenerator n (word mu))) * centeredDelta (commonBlock S m O) *
          centeredDelta (aggregate S m (dataOperator c rho)) else 0 := by sorry

end QAlgorithms.Papers.Independent.Support50.P30

end
