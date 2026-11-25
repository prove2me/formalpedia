-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_isTayF_comp
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.isTayF_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:25:46.758794+00:00
-- url     : https://prove2.me/theorems/16f11239-96fd-46c2-9c12-7aec4125b6b9
-- title:
--   TCPf: is Tay F comp
-- statement:
--   The TCPf construction uses the is Tay F comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorComp.lean#L114-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorComp.lean#L114-L119

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.isTayF_comp {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : V → ℂ} (hf : ContDiffAt ℂ ω f 0)
    (A : W →L[ℂ] V) {w : σ → W} {v : σ → V} (hv : ∀ q, A (w q) = v q) {F : MvPowerSeries σ ℂ}
    (hF : IsTayF f v F) : IsTayF (f ∘ A) w F := by sorry
