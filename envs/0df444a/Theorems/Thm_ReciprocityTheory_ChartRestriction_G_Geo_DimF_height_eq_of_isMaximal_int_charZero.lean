-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_height_eq_of_isMaximal_int_charZero
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_eq_of_isMaximal_int_charZero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:23:25.487217+00:00
-- url     : https://prove2.me/theorems/27ff5c21-6203-4b82-a4b6-f6f4f8ad071c
-- title:
--   Dim F: height eq of is Maximal int char Zero
-- statement:
--   The Dim F construction uses the height eq of is Maximal int char Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAB.lean#L266-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAB.lean#L266-L320

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_IsCMOfIsRegularLocalRing
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_RingKrullDimLocalizationQuotientEqHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.DimF

theorem ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_eq_of_isMaximal_int_charZero {σ : Type*} [Finite σ]
    (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime] (hP : P.comap MvPolynomial.C = ⊥)
    (M : Ideal (MvPolynomial σ ℤ ⧸ P)) (hM : M.IsMaximal) :
    (M.height : WithBot ℕ∞) = ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by sorry
