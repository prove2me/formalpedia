-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_height_add_height_map_eq_mvPolynomial_field
-- name    : ReciprocityTheory.CA.height_add_height_map_eq_mvPolynomial_field
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:29.069113+00:00
-- url     : https://prove2.me/theorems/018d0df9-0cb9-5512-ac9c-ee5e0913cb11
-- title:
--   CA: height add height map eq mv Polynomial field
-- statement:
--   The CA construction uses the height add height map eq mv Polynomial field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/HeightAddRingKrullDimQuotientMvPolynomialField.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/HeightAddRingKrullDimQuotientMvPolynomialField.lean#L30-L35

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

theorem ReciprocityTheory.CA.height_add_height_map_eq_mvPolynomial_field (K : Type*) [Field K] (N : ℕ)
    (𝔔 𝔐 : Ideal (MvPolynomial (Fin N) K)) [𝔔.IsPrime] [𝔐.IsMaximal] (hle : 𝔔 ≤ 𝔐) :
    𝔔.height + (𝔐.map (Ideal.Quotient.mk 𝔔)).height = N := by sorry
