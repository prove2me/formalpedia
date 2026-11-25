-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_cc_subst
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.cc_subst
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:11.247795+00:00
-- url     : https://prove2.me/theorems/f8a33996-74ed-4ce0-ab9d-6c27aa65a3b1
-- title:
--   TCPf: cc subst
-- statement:
--   The TCPf construction uses the cc subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorComp.lean#L175-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorComp.lean#L175-L195

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
variable {g : ℕ}
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.cc_subst {σ τ : Type} [Fintype σ] {L : σ → MvPowerSeries τ ℂ} (hL0 : ∀ p, constantCoeff (L p) = 0)
    (F : MvPowerSeries σ ℂ) : constantCoeff (subst L F) = constantCoeff F := by sorry
