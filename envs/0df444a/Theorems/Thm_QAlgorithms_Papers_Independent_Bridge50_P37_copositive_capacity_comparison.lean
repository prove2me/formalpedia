-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_copositive_capacity_comparison
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.copositive_capacity_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:46:11.263292+00:00
-- url     : https://prove2.me/theorems/37f050d2-29d9-45ad-8273-4f536fcb9b01
-- title:
--   Unnumbered result: completely co-positive choices cannot improve the transposition bound
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree. The symbols $\|\cdot\|_\diamond$, $\|\cdot\|_1$ and $\|\cdot\|_\infty$ denote the diamond, trace and spectral norms, respectively; $*$ denotes the Hilbert--Schmidt adjoint. Choi matrices and maximally entangled projections use the normalized, reference-first convention.
--
--   In Theorem 6, suppose $P=\vartheta_{d_2}\circ S$ where $S:M_{d_3}\to M_{d_2}$ is surjective, unital and CP, and retain that $P$ is not CP. Every right inverse $R$ of $P$ has the form $R=V\circ\vartheta_{d_2}$ for a right inverse $V$ of $S$. Writing $B(T,P,R)$ for Theorem 6's displayed expression,
--   $$B(T,P,R)\ge\log_2\!\bigl(\|V\circ\vartheta_{d_2}\circ T\|_\diamond\|S\|_\diamond\bigr)\ge\log_2\|\vartheta_{d_2}\circ T\|_\diamond\ge Q(T).$$
--   Also $\|P^*\|_\diamond\le d_2$, $\|P^*\|_{1\to1}=1$, and $\|P^*(I)\|_\infty=\|S^*(I)\|_\infty=\|S\|_\diamond$. Thus completely co-positive choices do not improve the transposition bound.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 9, Unnumbered result: completely co-positive choices cannot improve the transposition bound

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

/-- Unnumbered comparison, PDF pp.9--10: full inequality chain and inverse factorization.
The non-CP premise is inherited from Theorem 6, excluding a zero log denominator. -/
theorem copositive_capacity_comparison [Nonempty A] [Nonempty B] [Nonempty C]
    (T : MatrixMap A B) (S : MatrixMap C B) (R : MatrixMap B C) (hT : IsChannel T)
    (hS : Entanglement.IsCompletelyPositive S) (hs : Function.Surjective S) (hu : S 1 = 1)
    (hncp : ¬ Entanglement.IsCompletelyPositive ((basisTransposeLinearMap B).comp S))
    (hR : (((basisTransposeLinearMap B).comp S).comp R) = LinearMap.id) :
    let P := (basisTransposeLinearMap B).comp S
    ∃ V : MatrixMap B C, S.comp V = LinearMap.id ∧ R = V.comp (basisTransposeLinearMap B) ∧
      diamond (hsAdjoint P) ≤ Fintype.card B ∧ inducedTrace (hsAdjoint P) = 1 ∧
      specNorm (hsAdjoint P 1) = specNorm (hsAdjoint S 1) ∧
      specNorm (hsAdjoint S 1) = diamond S ∧
      capacityBound T P R ≥ Real.logb 2 (diamond (V.comp ((basisTransposeLinearMap B).comp T)) * diamond S) ∧
      Real.logb 2 (diamond (V.comp ((basisTransposeLinearMap B).comp T)) * diamond S) ≥
        Real.logb 2 (diamond ((basisTransposeLinearMap B).comp T)) ∧
      Real.logb 2 (diamond ((basisTransposeLinearMap B).comp T)) ≥ diamondQuantumCapacity T := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
