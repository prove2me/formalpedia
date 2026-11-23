-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_height_add_height_maximal_quotient_field
-- name    : ReciprocityTheory.CA.height_add_height_maximal_quotient_field
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:25:05.546275+00:00
-- url     : https://prove2.me/theorems/06d26602-f825-410f-9998-7433ebfef435
-- title:
--   CA: height add height maximal quotient field
-- statement:
--   The CA construction uses the height add height maximal quotient field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/HeightAddRingKrullDimQuotientMvPolynomialField.lean#L37-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/HeightAddRingKrullDimQuotientMvPolynomialField.lean#L37-L46

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

theorem ReciprocityTheory.CA.height_add_height_maximal_quotient_field (K : Type*) [Field K] (N : ℕ)
    (𝔔 : Ideal (MvPolynomial (Fin N) K)) [𝔔.IsPrime]
    (𝔪 : Ideal (MvPolynomial (Fin N) K ⧸ 𝔔)) [h𝔪 : 𝔪.IsMaximal] :
    𝔔.height + 𝔪.height = N := by sorry
