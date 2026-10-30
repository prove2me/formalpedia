-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_right_inverse_capacity_bound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.right_inverse_capacity_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:44:22.988767+00:00
-- url     : https://prove2.me/theorems/828ef3e5-8887-4be7-a274-c12134982c35
-- title:
--   Theorem 6: capacity bound from a right-invertible tensor-stable map
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree. The symbols $\|\cdot\|_\diamond$, $\|\cdot\|_1$ and $\|\cdot\|_\infty$ denote the diamond, trace and spectral norms, respectively; $*$ denotes the Hilbert--Schmidt adjoint. Choi matrices and maximally entangled projections use the normalized, reference-first convention.
--
--   Let $T:M_{d_1}\to M_{d_2}$ be a channel, $P:M_{d_3}\to M_{d_2}$ a surjective unital tensor-stable positive map that is not CP, and $R:M_{d_2}\to M_{d_3}$ any complex-linear right inverse, $P\circ R=\mathrm{id}$. Then
--   $$Q(T)\le\frac{\log_2\!\bigl(\|R\circ T\|_\diamond\|P^*(I_{d_2})\|_\infty\bigr)\log_2d_2}{\log_2\|P^*\|_\diamond}.$$
--   Here $Q$ is the unassisted quantum capacity defined by vanishing optimized half-diamond coding error and a limsup rate. The logarithm encloses the product. The right inverse need not be positive or CP; $\|P^*\|_\diamond>1$ follows from the map hypotheses.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 8, Theorem 6: capacity bound from a right-invertible tensor-stable map

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

/-- Theorem 6, PDF pp.8--9: arbitrary complex-linear right inverse, product INSIDE log.
Positivity of its denominator is a consequence, never an extra hypothesis. -/
theorem right_inverse_capacity_bound [Nonempty A] [Nonempty B] [Nonempty C]
    (T : MatrixMap A B) (P : MatrixMap C B) (R : MatrixMap B C) (hT : IsChannel T)
    (hP : TensorStable P) (hs : Function.Surjective P) (hu : P 1 = 1)
    (hncp : ¬ Entanglement.IsCompletelyPositive P) (hR : P.comp R = LinearMap.id) :
    diamondQuantumCapacity T ≤ capacityBound T P R := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
