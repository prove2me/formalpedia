-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_complementary_mutual_identity
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.complementary_mutual_identity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:41:01.251313+00:00
-- url     : https://prove2.me/theorems/275fb7ed-b371-4b47-96d6-4cf650a0a687
-- title:
--   Theorem 1: complementary-channel mutual-information identity (22)
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. Let $\Phi$ and $\widetilde\Phi$ be the two partial-trace channels of the same isometry $V:\mathcal H_A\to\mathcal H_B\otimes\mathcal H_E$. For every input state $\rho$,
--
--   $$I(\rho,\Phi)+I(\rho,\widetilde\Phi)=2H(\rho).$$
--
--   The equality holds in $[0,+\infty]$, including infinite input entropy, and gives the basic complementary-channel identity.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 13, Theorem 1: complementary-channel mutual-information identity (22)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Theorem 1, equation (22), PDF pp.13–15. No finite-entropy restriction. -/
theorem complementary_mutual_identity [Countable I] [Countable J] [Countable E] (rho : State I)
    (Phi : Channel I J) (Psi : Channel I E) (hcomp : Complementary Phi Psi) :
    mutualInformation rho.coefficients Phi.val + mutualInformation rho.coefficients Psi.val =
      2 * homogeneousEntropy rho.coefficients := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
