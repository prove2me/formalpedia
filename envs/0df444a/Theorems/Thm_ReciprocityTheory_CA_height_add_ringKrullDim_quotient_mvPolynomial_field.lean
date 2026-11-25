-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_height_add_ringKrullDim_quotient_mvPolynomial_field
-- name    : ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:02.605223+00:00
-- url     : https://prove2.me/theorems/fd2bdb11-f96d-41c3-a719-127b91d03e23
-- title:
--   CA: height add ring Krull Dim quotient mv Polynomial field
-- statement:
--   The CA construction uses the height add ring Krull Dim quotient mv Polynomial field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/HeightAddRingKrullDimQuotientMvPolynomialField.lean#L48-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/HeightAddRingKrullDimQuotientMvPolynomialField.lean#L48-L75

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

theorem ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field (K : Type*) [Field K] (N : ℕ)
    (𝔔 : Ideal (MvPolynomial (Fin N) K)) [𝔔.IsPrime] :
    (𝔔.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin N) K ⧸ 𝔔) = N := by sorry
