-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P17_order_chain_projections
-- name    : QAlgorithms.Papers.Independent.Support21.P17.order_chain_projections
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:47:02.549999+00:00
-- url     : https://prove2.me/theorems/df9b5121-e941-47ac-91d3-abfca01f9ac5
-- title:
--   Projection realization of finite order chains
-- statement:
--   Let $H,K$ be complex separable Hilbert spaces with $H\ne0$, let $n\ge1$, and let $T_1,\ldots,T_n:B(H)\to B(K)$ be normal CP maps satisfying $T_i(I_H)\le I_K$. Then
--
--   $$T_1\le\cdots\le T_n\iff\exists E,V,(P_i)_{i=1}^n,\quad T_i(A)=V^*(A\otimes P_i)V,\qquad P_1\le\cdots\le P_n.$$
--
--   Here $E$ is a separable Hilbert space, $V:K\to H\otimes E$ is an isometry, and each $P_i$ is a self-adjoint idempotent. The projections are nested, rather than pairwise orthogonal. This realizes the order chain on one enlarged environment, without a finite-dimensional restriction.
-- source:
--   Radon-Nikodym derivatives of quantum operations, arXiv:math-ph/0303056v3, PDF p. 13, Theorem 4.2: projection realization of finite order chains

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P17

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker Topology TensorProduct

open Filter

namespace QAlgorithms.Papers.Independent.Support21.P17

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)

open QAlgorithms.Papers.Independent.Next46.P33 (UltraweakTest)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin coefficientMap)

/-- Theorem 4.2, PDF p.13: order chains of operations are precisely compressions of
nested orthogonal projections. "Orthogonal" describes each projection, not pairwise
orthogonality. Printed: no nonzero-input hypothesis. Changed: H is nonzero.
Why: H=0, K nonzero and every T_i=0 satisfy the printed hypotheses but admit
no isometry K → H tensor E; the added hypothesis excludes exactly this obstruction. -/
theorem order_chain_projections (H K : SeparableHilbertSpace) [Nontrivial H]
    (n : ℕ) (hn : 0 < n) (T : Fin n → HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K)
    (hT : ∀ i, IsSubunitalNormalCP (T i)) :
    (∀ i j, i ≤ j → CompletelyDominated (T i) (T j)) ↔
    ∃ E : SeparableHilbertSpace, ∃ V : K →ₗᵢ[ℂ] NoiseSpace H E, ∃ P : Fin n → HilbertEndomorphism E,
      (∀ i, ContinuousLinearMap.adjoint (P i) = P i ∧ (P i).comp (P i) = P i) ∧
      (∀ i j, i ≤ j → (P j - P i).IsPositive) ∧
      ∀ i A, T i A = compress V.toContinuousLinearMap (completedTensorMap A (P i)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P17

end
