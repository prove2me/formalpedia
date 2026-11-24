-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_h_eq_of_sameOrbit
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.h_eq_of_sameOrbit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:36.881297+00:00
-- url     : https://prove2.me/theorems/605cca96-93a6-4a73-a574-590307c77a58
-- title:
--   Geo: h eq of same Orbit
-- statement:
--   The Geo construction uses the h eq of same Orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedA.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedA.lean#L43-L47

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.h_eq_of_sameOrbit {B : HermLine ι} (hB : B.a = 0) {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : B.h z = B.h z' := by sorry
