-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_purification_independence
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.purification_independence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:41:50.740081+00:00
-- url     : https://prove2.me/theorems/4ec4a99e-ab4e-4f66-9e9a-a2d617655323
-- title:
--   Remark 1: independence of reference and purification
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. For any input state $\rho$, channel $\Phi$, reference space $\mathcal H_R$, and pure state $\psi_{AR}$ with marginal $\rho$, let $\psi_R=\operatorname{Tr}_A\psi_{AR}$. Then
--
--   $$D\big((\Phi\otimes\operatorname{Id}_R)(\psi_{AR})\,\Vert\,\Phi(\rho)\otimes\psi_R\big)=I(\rho,\Phi).$$
--
--   Thus the value is independent of both the reference space and the purification, including its global phase.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 6, Remark 1: independence of reference and purification

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Remark 1, PDF p.6: every reference and every purification give Definition 4. -/
theorem purification_independence [Countable I] [Countable J] [Countable R] (rho : State I) (Phi : Channel I J)
    (psi : PureState (I × R)) (hp : Purifies psi rho.coefficients) :
    generalizedRelativeEntropy (tensorApply Phi.val psi.val.coefficients)
      (productCoeff (Phi.val rho.coefficients) (traceFirst psi.val.coefficients)) =
      mutualInformation rho.coefficients Phi.val := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
