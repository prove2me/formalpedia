-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_output_entropy_difference
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.output_entropy_difference
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:45:37.785519+00:00
-- url     : https://prove2.me/theorems/b377fb41-846f-401d-971f-b6d26acbe1e2
-- title:
--   Equation (23): consistency with output-entropy difference
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. Let $\Phi$ and $\widetilde\Phi$ be complementary through one isometry, and suppose $H(\rho)<\infty$ and $H(\Phi(\rho))<\infty$. The complementary output entropy is finite as well, and
--
--   $$\begin{aligned}I(\rho,\Phi)&=H(\rho)+H(\Phi(\rho))-H(\widetilde\Phi(\rho)),\\ I_c(\rho,\Phi)&=H(\Phi(\rho))-H(\widetilde\Phi(\rho)).\end{aligned}$$
--
--   Here $I_c=I-H(\rho)$ is real coherent information. The result establishes consistency with the conventional output-entropy difference on its valid domain.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 15, Equation (23): consistency with output-entropy difference

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Equation (23), PDF pp.15–16. Complementary output finiteness is a conclusion,
not an assumed restriction needed to evade an infinite entropy difference. -/
theorem output_entropy_difference [Countable I] [Countable J] [Countable E] (rho : State I) (Phi : Channel I J) (Psi : Channel I E)
    (hcomp : Complementary Phi Psi) (hin : homogeneousEntropy rho.coefficients < ⊤)
    (hout : homogeneousEntropy (Phi.val rho.coefficients) < ⊤) :
    homogeneousEntropy (Psi.val rho.coefficients) < ⊤ ∧
    (mutualInformation rho.coefficients Phi.val).toReal = (homogeneousEntropy rho.coefficients).toReal +
      (homogeneousEntropy (Phi.val rho.coefficients)).toReal - (homogeneousEntropy (Psi.val rho.coefficients)).toReal ∧
    finiteInputCoherentInfo rho.coefficients Phi.val = (homogeneousEntropy (Phi.val rho.coefficients)).toReal -
      (homogeneousEntropy (Psi.val rho.coefficients)).toReal := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
