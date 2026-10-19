-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P07_jointKernel_obstruction
-- name    : QAlgorithms.Papers.Independent.Information100.P07.jointKernel_obstruction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:33:09.590584+00:00
-- url     : https://prove2.me/theorems/271b3c91-76ce-4cd8-b235-0e5cba629884
-- title:
--   Lemma E1: joint-kernel obstruction
-- statement:
--   Let $\eta\ge0$ act on $\mathbb C^3\otimes\mathbb C^3$, with completely entangled range and Alice local rank three. Let $D$ be Hermitian with precisely one negative, one zero and one positive eigenvalue. Writing $P_{\rm supp}$ for the support projection and $P_\pm$ for the full positive and negative spectral projections, the two equations
--   $$P_{\rm supp\eta}(D\otimes I)P_{\rm supp\eta}=0,\qquad P_+(\eta^\Gamma)(D^T\otimes I)P_-(\eta^\Gamma)=0$$
--   cannot both hold. Here $\Gamma=T_A$ in the computational basis. Neither normalization of $\eta$ nor invertibility of its partial transpose is required.
--
--   This is the joint-kernel obstruction used for singular as well as nonsingular partial transposes.
-- source:
--   Complete Classification of Reversible Entanglement Transformations of Two Qutrits, arXiv:2610.05234v1, PDF p. 5, Lemma E1: joint-kernel obstruction

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:2610.05234v1, PDF p.5, Lemma E1: joint-kernel obstruction. -/
theorem jointKernel_obstruction (eta : Joint) (D : Local)
    (heta : eta.PosSemidef) (hces : IsCES (operatorRange eta))
    (hrank : (localRanks (operatorRange eta)).1 = 3) (hD : D.IsHermitian)
    (hneg : ascEigenvalues D 0 < 0) (hzero : ascEigenvalues D 1 = 0)
    (hpos : 0 < ascEigenvalues D 2) :
    ¬ (support eta * Matrix.kronecker D 1 * support eta = 0 ∧
      positiveProjection (partialTransposeFirst eta) * Matrix.kronecker D.transpose 1 *
        negativeProjection (partialTransposeFirst eta) = 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P07

end
