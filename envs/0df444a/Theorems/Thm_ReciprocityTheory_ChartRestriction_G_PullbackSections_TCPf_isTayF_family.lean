-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_isTayF_family
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.isTayF_family
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:25:22.953565+00:00
-- url     : https://prove2.me/theorems/86dcb00f-c1a8-47d5-812e-d7cdd1499bbe
-- title:
--   TCPf: is Tay F family
-- statement:
--   The TCPf construction uses the is Tay F family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorComp.lean#L103-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorComp.lean#L103-L112

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
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.isTayF_family (Θ : W → ℂ) (w : σ → W) (Φ : Multiset W → MvPowerSeries σ ℂ)
    (hd : ∀ q s, pderiv ℂ q (Φ s) = Φ (w q ::ₘ s)) (hc : ∀ s, constantCoeff (Φ s) = mD Θ 0 s) :
    IsTayF Θ w (Φ 0) := by sorry
