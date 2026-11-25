-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_iter_comp_clm
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.iter_comp_clm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:23.508452+00:00
-- url     : https://prove2.me/theorems/be50779e-aae9-4549-afaf-64be5a33a4a3
-- title:
--   TCPf: iter comp clm
-- statement:
--   The TCPf construction uses the iter comp clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorComp.lean#L17-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorComp.lean#L17-L28

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
variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.iter_comp_clm {f : V → ℂ} (hf : ContDiffAt ℂ ω f 0) (A : W →L[ℂ] V) (i : ℕ) :
    iteratedFDeriv ℂ i (f ∘ A) 0 = (iteratedFDeriv ℂ i f 0).compContinuousLinearMap fun _ => A := by sorry
