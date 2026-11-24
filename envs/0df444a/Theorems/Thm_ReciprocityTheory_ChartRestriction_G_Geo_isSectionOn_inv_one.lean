-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isSectionOn_inv_one
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.isSectionOn_inv_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:25:44.21494+00:00
-- url     : https://prove2.me/theorems/1930d267-6122-40f2-a4fc-5d2cd7338218
-- title:
--   Geo: is Section On inv one
-- statement:
--   The Geo construction uses the is Section On inv one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedA.lean#L29-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedA.lean#L29-L41

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology MeasureTheory
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.isSectionOn_inv_one {P : Ideal (MRing ι)} (hP : P.IsPrime) {B : HermLine ι}
    (hB : B.a = 0) : IsSectionOn P B.inv 1 := by sorry
