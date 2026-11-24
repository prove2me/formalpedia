-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_height_maximal_mvPolynomial_field
-- name    : ReciprocityTheory.CA.height_maximal_mvPolynomial_field
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:56.741119+00:00
-- url     : https://prove2.me/theorems/273e418d-72b5-4655-aa66-7248c35912a7
-- title:
--   CA: height maximal mv Polynomial field
-- statement:
--   The CA construction uses the height maximal mv Polynomial field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/HeightAddRingKrullDimQuotientMvPolynomialField.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/HeightAddRingKrullDimQuotientMvPolynomialField.lean#L21-L28

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

theorem ReciprocityTheory.CA.height_maximal_mvPolynomial_field (K : Type*) [Field K] (N : ℕ)
    (𝔐 : Ideal (MvPolynomial (Fin N) K)) [𝔐.IsMaximal] :
    IsCM (Localization.AtPrime 𝔐) ∧ 𝔐.height = N := by sorry
