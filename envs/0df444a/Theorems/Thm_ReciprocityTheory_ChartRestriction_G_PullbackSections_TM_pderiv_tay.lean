-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_pderiv_tay
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.TM.pderiv_tay
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:25.765036+00:00
-- url     : https://prove2.me/theorems/bddf6f97-24ce-41a3-bd3e-37c08e83d694
-- title:
--   TM: pderiv tay
-- statement:
--   The TM construction uses the pderiv tay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorMul.lean#L108-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorMul.lean#L108-L130

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorMul
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology
variable {g : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.TM.pderiv_tay {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (j : Fin g) :
    pderiv ℂ ((0 : Fin 1), j) (tay θ 0) = tay (fun y => fderiv ℂ θ y (Pi.single j 1)) 0 := by sorry
