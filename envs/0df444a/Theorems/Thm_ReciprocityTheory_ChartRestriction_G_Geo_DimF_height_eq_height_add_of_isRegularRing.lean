-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_height_eq_height_add_of_isRegularRing
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_eq_height_add_of_isRegularRing
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:26.870004+00:00
-- url     : https://prove2.me/theorems/882fe0c1-63d5-42b4-916b-b8475fd9533e
-- title:
--   Dim F: height eq height add of is Regular Ring
-- statement:
--   The Dim F construction uses the height eq height add of is Regular Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAB.lean#L194-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAB.lean#L194-L207

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_eq_height_add_of_isRegularRing {R : Type*} [CommRing R] [IsRegularRing R]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) :
    q.height = p.height + (q.map (Ideal.Quotient.mk p)).height := by sorry
