-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_coherent_chi_difference
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.coherent_chi_difference
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:48:01.218277+00:00
-- url     : https://prove2.me/theorems/8e333320-d430-453b-9504-bdc234a20eac
-- title:
--   Remark 2 and Example 2: coherent information as a chi-function difference
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. Let $\Phi,\widetilde\Phi$ be complementary and $H(\rho)<\infty$. Define the chi function at the fixed input $\rho$ by
--
--   $$\chi_\Phi(\rho)=\sup_{\sum_i p_i\rho_i=\rho}\sum_i p_iD(\Phi(\rho_i)\Vert\Phi(\rho)).$$
--
--   The supremum ranges over finite or countable state ensembles. Both chi functions are finite and
--
--   $$I_c(\rho,\Phi)=\chi_\Phi(\rho)-\chi_{\widetilde\Phi}(\rho).$$
--
--   This representation remains valid when either output entropy is infinite; optimization over other barycenters is not involved.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 16, Remark 2 and Example 2: coherent information as a chi-function difference

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Remark 2 and Example 2, equation (25), PDF pp.16,22. Chi is optimized at the
fixed barycenter rho; finite receiver entropy is not required. -/
theorem coherent_chi_difference [Countable I] [Countable J] [Countable E] (rho : State I) (Phi : Channel I J) (Psi : Channel I E)
    (hcomp : Complementary Phi Psi) (hin : homogeneousEntropy rho.coefficients < ⊤) :
    barycentricChi rho.coefficients Phi.val < ⊤ ∧ barycentricChi rho.coefficients Psi.val < ⊤ ∧
    finiteInputCoherentInfo rho.coefficients Phi.val =
      (barycentricChi rho.coefficients Phi.val).toReal - (barycentricChi rho.coefficients Psi.val).toReal := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
