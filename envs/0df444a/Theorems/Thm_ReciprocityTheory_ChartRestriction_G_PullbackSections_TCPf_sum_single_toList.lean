-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_sum_single_toList
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.sum_single_toList
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:37.588222+00:00
-- url     : https://prove2.me/theorems/70215516-f855-459a-8db7-1934fbbf9ca4
-- title:
--   TCPf: sum single to List
-- statement:
--   The TCPf construction uses the sum single to List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorComp.lean#L68-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorComp.lean#L68-L82

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology
variable {σ : Type}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.sum_single_toList (k : σ →₀ ℕ) :
    ((Finsupp.toMultiset k).toList.map fun q => Finsupp.single q 1).sum = k := by sorry
