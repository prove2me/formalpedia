-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_height_eq_of_isMaximal_of_intCast_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_eq_of_isMaximal_of_intCast_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:24.665862+00:00
-- url     : https://prove2.me/theorems/6e7860e2-7480-44c7-af02-7b3f511cb87d
-- title:
--   Dim F: height eq of is Maximal of int Cast eq zero
-- statement:
--   The Dim F construction uses the height eq of is Maximal of int Cast eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAB.lean#L16-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAB.lean#L16-L32

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_eq_of_isMaximal_of_intCast_eq_zero {B : Type*} [CommRing B] [IsDomain B]
    [Algebra.FiniteType ℤ B] (n : ℤ) (hn0 : n ≠ 0) (hnB : (n : B) = 0)
    (M N : Ideal B) (hM : M.IsMaximal) (hN : N.IsMaximal) : M.height = N.height := by sorry
