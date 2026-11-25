-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_comap_C_eq_maximalIdeal_field
-- name    : ReciprocityTheory.CA.comap_C_eq_maximalIdeal_field
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:38:43.119577+00:00
-- url     : https://prove2.me/theorems/e70eb433-b0d4-5ebe-9bc6-f164c0c91a4a
-- title:
--   CA: comap C eq maximal Ideal field
-- statement:
--   The CA construction uses the comap C eq maximal Ideal field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/HeightAddRingKrullDimQuotientMvPolynomialField.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/HeightAddRingKrullDimQuotientMvPolynomialField.lean#L12-L19

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
universe u

theorem ReciprocityTheory.CA.comap_C_eq_maximalIdeal_field (K : Type*) [Field K] (N : ℕ)
    (𝔐 : Ideal (MvPolynomial (Fin N) K)) [𝔐.IsMaximal] :
    𝔐.comap MvPolynomial.C = IsLocalRing.maximalIdeal K := by sorry
