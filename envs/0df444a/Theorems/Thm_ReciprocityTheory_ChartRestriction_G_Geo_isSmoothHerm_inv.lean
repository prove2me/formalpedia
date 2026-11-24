-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isSmoothHerm_inv
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:25:28.887171+00:00
-- url     : https://prove2.me/theorems/bac98d06-0dcc-4c9b-9f61-20920ea7709e
-- title:
--   Geo: is Smooth Herm inv
-- statement:
--   The Geo construction uses the is Smooth Herm inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedA.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedA.lean#L26-L27

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_inv {B : HermLine ι} (hB : IsSmoothHerm B) : IsSmoothHerm B.inv := by sorry
