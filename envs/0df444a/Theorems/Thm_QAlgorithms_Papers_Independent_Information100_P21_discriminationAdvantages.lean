-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_discriminationAdvantages
-- name    : QAlgorithms.Papers.Independent.Information100.P21.discriminationAdvantages
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:09:07.257843+00:00
-- url     : https://prove2.me/theorems/f9e7cb09-74ec-47fa-a92d-bad2aa763469
-- title:
--   VIII — relationship between the two discrimination advantages
-- statement:
--   For a two-qubit state $\rho$, define $A_{\rm gen}$ by success-probability ratios for arbitrary finite channel ensembles, sharing one fixed POVM between numerator and the separable-input denominator. Define $A_{\rm bin}$ for equiprobable binary channels using ratios of gains above $1/2$, optimizing the POVM separately for each input. Include only positive denominators. Then
--   $$A_{\rm bin}(\rho)=2A_{\rm gen}(\rho)-1.$$
--   Channels and output measurements are unrestricted, without an additional entangled reference. The equality relates two distinct tasks.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 23, VIII — relationship between the two discrimination advantages

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 23, relationship between the two discrimination advantages. -/
theorem discriminationAdvantages (rho : Op QQ) (h : QAlgorithms.IsDensityMatrix rho) :
  advantageBinary rho=2*advantageGeneral rho-1 := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
