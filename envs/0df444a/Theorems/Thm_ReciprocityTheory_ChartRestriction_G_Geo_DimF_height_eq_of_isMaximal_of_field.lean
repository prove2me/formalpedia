-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_height_eq_of_isMaximal_of_field
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_eq_of_isMaximal_of_field
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:22.838939+00:00
-- url     : https://prove2.me/theorems/41150fbc-405b-4cf9-b709-6631320119ab
-- title:
--   Dim F: height eq of is Maximal of field
-- statement:
--   The Dim F construction uses the height eq of is Maximal of field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAB.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAB.lean#L10-L14

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_eq_of_isMaximal_of_field {k B : Type*} [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] (M N : Ideal B) (hM : M.IsMaximal) (hN : N.IsMaximal) :
    M.height = N.height := by sorry
