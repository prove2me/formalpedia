-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_lD_perm
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.lD_perm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:25:52.594414+00:00
-- url     : https://prove2.me/theorems/a28a87d7-0b76-476c-8430-b6613e1f7cb0
-- title:
--   Pullback Sections: l D perm
-- statement:
--   The Pullback Sections construction uses the l D perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean#L69-L73

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.lD_perm {φ : V → ℂ} {x : V} (hφ : ContDiffAt ℂ ω φ x) {l l' : List V} (p : l.Perm l') :
    lD φ x l = lD φ x l' := by sorry
