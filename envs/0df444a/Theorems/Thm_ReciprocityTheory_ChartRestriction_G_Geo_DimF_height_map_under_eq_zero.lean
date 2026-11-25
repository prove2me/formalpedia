-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_height_map_under_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_map_under_eq_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:22:53.149431+00:00
-- url     : https://prove2.me/theorems/fc124691-f578-44f8-8b27-38c12ffb8609
-- title:
--   Dim F: height map under eq zero
-- statement:
--   The Dim F construction uses the height map under eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAC.lean#L35-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAC.lean#L35-L70

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
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
open Ideal

theorem ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_map_under_eq_zero {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.IsIntegral R B] (M : Ideal B) [M.IsPrime] :
    (M.map (Ideal.Quotient.mk ((M.under R).map (algebraMap R B)))).height = 0 := by sorry
