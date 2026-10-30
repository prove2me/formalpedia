-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_diamond_norm_properties
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.diamond_norm_properties
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:40:03.665926+00:00
-- url     : https://prove2.me/theorems/a0333a85-dbcf-4d82-b6c6-d94a3d710b7a
-- title:
--   Lemma 2: three diamond-norm properties
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree. The symbols $\|\cdot\|_\diamond$, $\|\cdot\|_1$ and $\|\cdot\|_\infty$ denote the diamond, trace and spectral norms, respectively; $*$ denotes the Hilbert--Schmidt adjoint. Choi matrices and maximally entangled projections use the normalized, reference-first convention.
--
--   For a completely positive map $T:M_{d_1}\to M_{d_2}$,
--   $$\|T\|_\diamond=\|T\|_{1\to1}=\|T^*\|_{\infty\to\infty}=\|T^*(I_{d_2})\|_\infty.$$
--   For every complex-linear $L:M_{d_1}\to M_{d_2}$, every positive $n$, and arbitrary composable complex-linear maps $L_1,L_2$,
--   $$\|L^{\otimes n}\|_\diamond=\|L\|_\diamond^n,\qquad\|L_2\circ L_1\|_\diamond\le\|L_2\|_\diamond\|L_1\|_\diamond.$$
--   The induced norms act on all matrices. Only the first clause requires CP; none requires trace preservation. The source attributes these properties to Paulsen [24].
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 4, Lemma 2: three diamond-norm properties

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

/-- Lemma 2, PDF pp.4--5, attributed there to Paulsen [24]: all three clauses;
only the first clause assumes complete positivity, and none assumes TP. -/
theorem diamond_norm_properties [Nonempty A] [Nonempty B] [Nonempty C] :
    (∀ T : MatrixMap A B, Entanglement.IsCompletelyPositive T →
      diamond T = inducedTrace T ∧ inducedTrace T = inducedInfinity (hsAdjoint T) ∧
        inducedInfinity (hsAdjoint T) = specNorm (hsAdjoint T 1)) ∧
    (∀ L : MatrixMap A B, ∀ n : ℕ, 0 < n → diamond (tensorLinearPower L n) = diamond L ^ n) ∧
    (∀ L1 : MatrixMap A B, ∀ L2 : MatrixMap B C,
      diamond (L2.comp L1) ≤ diamond L2 * diamond L1) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
