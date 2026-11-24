-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isSectionOn_one
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.isSectionOn_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:52.642381+00:00
-- url     : https://prove2.me/theorems/04fa1e55-fe59-41bf-990c-c8bf41d1f3e2
-- title:
--   Geo: is Section On one
-- statement:
--   The Geo construction uses the is Section On one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedF.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedF.lean#L25-L32

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
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
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.isSectionOn_one {P : Ideal (MRing ι)} (hP : P.IsPrime) {B : HermLine ι} (hB : B.a = 0) :
    IsSectionOn P B 1 := by sorry
