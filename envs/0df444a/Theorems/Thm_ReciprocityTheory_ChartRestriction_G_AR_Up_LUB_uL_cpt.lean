-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUB_uL_cpt
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.LUB.uL_cpt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:07:21.766406+00:00
-- url     : https://prove2.me/theorems/aa465302-9df9-5979-af44-f3ee88683a0a
-- title:
--   LUB: u L cpt
-- statement:
--   The LUB construction uses the u L cpt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LocalUnfoldPfC.lean#L44-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LocalUnfoldPfC.lean#L44-L53

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LocalUnfoldPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LocalUnfoldPfC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')
variable {X b1}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.LUB.uL_cpt (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) (z : V (nd X)) (b : Frame X.Ψ r) :
    uL X x1' b1 (rmul (cpt X (rmul x1' b1) z) b) = rmul (cpt X x1' z) b := by sorry
