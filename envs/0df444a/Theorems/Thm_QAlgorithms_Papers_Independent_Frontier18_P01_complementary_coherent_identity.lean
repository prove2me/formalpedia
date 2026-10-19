-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_complementary_coherent_identity
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.complementary_coherent_identity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:47:16.902899+00:00
-- url     : https://prove2.me/theorems/92e6dc5d-9b2d-49a5-987c-ea19efec0658
-- title:
--   Corollary 1: complementary coherent informations sum to zero
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. For a complementary pair $\Phi,\widetilde\Phi$ arising from the same isometry and any state $\rho$ with finite input entropy, real coherent informations satisfy
--
--   $$I_c(\rho,\Phi)+I_c(\rho,\widetilde\Phi)=0.$$
--
--   Each term is defined by $I_c=I-H(\rho)$. This is the coherent-information counterpart of the complementary mutual-information identity.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 16, Corollary 1: complementary coherent informations sum to zero

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Corollary 1, equation (24), PDF p.16. The equality is in the reals. -/
theorem complementary_coherent_identity [Countable I] [Countable J] [Countable E] (rho : State I)
    (Phi : Channel I J) (Psi : Channel I E) (hcomp : Complementary Phi Psi)
    (hin : homogeneousEntropy rho.coefficients < ⊤) :
    finiteInputCoherentInfo rho.coefficients Phi.val + finiteInputCoherentInfo rho.coefficients Psi.val = 0 := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
