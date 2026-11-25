-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_dof_iter_tay
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.dof_iter_tay
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:32:37.14772+00:00
-- url     : https://prove2.me/theorems/d8ce7861-629e-47df-8126-4829debb8714
-- title:
--   Pullback Sections: dof iter tay
-- statement:
--   The Pullback Sections construction uses the dof iter tay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean#L197-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean#L197-L203

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
variable {g : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.dof_iter_tay {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (v : Fin g → ℂ) (k : ℕ)
    (s : Multiset (Fin g → ℂ)) :
    (Dof (addF ℂ g) v)^[k] (tay θ s) = tay θ (Multiset.replicate k v + s) := by sorry
