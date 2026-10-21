-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P03_finite_vectorization_phiPlus
-- name    : QAlgorithms.Papers.Independent.Renew46.P03.finite_vectorization_phiPlus
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:54:51.086272+00:00
-- url     : https://prove2.me/theorems/9db8faa2-07de-44e0-b421-6a10ae3dee15
-- title:
--   Equation (2.1): finite-dimensional vectorization via phi_plus
-- statement:
--   Let $H$ be a finite-dimensional complex Hilbert space with complete orthonormal basis $(\phi_j)_{j=1}^n$, and let $A:H\to H$ be bounded and complex-linear. Define $T_B(A)=\sum_j\phi_j\otimes A\phi_j$ and the unnormalized vector $\phi_+=\sum_j\phi_j\otimes\phi_j$. Then
--
--   $$T_B(A)=(I_H\otimes A)\phi_+.$$
--
--   The tensor product is the Hilbert tensor product. No factor $1/\sqrt n$ is inserted; dimension zero gives zero on both sides. This expresses finite vectorization as an operator applied to a fixed entangled vector.
-- source:
--   Operator Isomorphisms on Hilbert Space Tensor Products, arXiv:2010.15901v1, PDF p. 9, Equation (2.1)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P03

universe u v

open QAlgorithms.Papers.Independent.Claimed50.P34 (HilbertTensor)

/-- Equation (2.1), PDF p.9: finite vectorization is the action of I tensor A
on unnormalized phi_plus. The result includes dimension zero. -/
theorem finite_vectorization_phiPlus
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ H) (A : H →L[ℂ] H) :
    finiteVectorization b A =
      completedTensorAction (ContinuousLinearMap.id ℂ H) A (unnormalizedBasisTensor b) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P03

end
