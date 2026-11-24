-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_height_add_height_map_le
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_add_height_map_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:02.839859+00:00
-- url     : https://prove2.me/theorems/9effd9a7-cbdc-457f-a72f-c058ae4f0a10
-- title:
--   Dim F: height add height map le
-- statement:
--   The Dim F construction uses the height add height map le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAA.lean#L25-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAA.lean#L25-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAA
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
variable {A : Type*} [CommRing A]

theorem ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_add_height_map_le [IsNoetherianRing A] [FiniteRingKrullDim A] {q M : Ideal A}
    [q.IsPrime] [M.IsPrime] (h : q ≤ M) :
    q.height + (M.map (Ideal.Quotient.mk q)).height ≤ M.height := by sorry
