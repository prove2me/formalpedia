-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_ringKrullDim_eq_of_trdeg_eq_field
-- name    : ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:02.691787+00:00
-- url     : https://prove2.me/theorems/a5a82ac0-b0fd-419c-9bc1-1f32502bdb73
-- title:
--   CA: ring Krull Dim eq of trdeg eq field
-- statement:
--   The CA construction uses the ring Krull Dim eq of trdeg eq field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/HeightAddRingKrullDimQuotientMvPolynomialField.lean#L99-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/HeightAddRingKrullDimQuotientMvPolynomialField.lean#L99-L105

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

theorem ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field {K A : Type u} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (n : ℕ) (h : Algebra.trdeg K A = n) :
    ringKrullDim A = n := by sorry
