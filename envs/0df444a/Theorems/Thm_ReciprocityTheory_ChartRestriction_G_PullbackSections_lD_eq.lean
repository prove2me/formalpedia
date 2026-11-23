-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_lD_eq
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.lD_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:55:30.638605+00:00
-- url     : https://prove2.me/theorems/57041cc9-087b-44e2-b54f-f74700978fdb
-- title:
--   Pullback Sections: l D eq
-- statement:
--   The Pullback Sections construction uses the l D eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean#L64-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean#L64-L67

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped ContDiff
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.lD_eq (φ : V → ℂ) (x : V) (l : List V) {n : ℕ} (h : l.length = n) :
    lD φ x l = iteratedFDeriv ℂ n φ x (fun i => l.get (i.cast h.symm)) := by sorry
