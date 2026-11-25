-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_divSupp_one
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.divSupp_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:23:29.389931+00:00
-- url     : https://prove2.me/theorems/4c14feaf-94b9-4fe5-93e2-fd8cdb639565
-- title:
--   Geo: div Supp one
-- statement:
--   The Geo construction uses the div Supp one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDerived.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDerived.lean#L11-L19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDerived
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.AI.I2
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.divSupp_one (P : Ideal (MRing ι)) : divSupp P 1 = ∅ := by sorry
