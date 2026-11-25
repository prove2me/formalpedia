-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_BigB_S_pos
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.BigB.S_pos
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:10:07.161667+00:00
-- url     : https://prove2.me/theorems/3243daa2-372b-452c-b7ea-e0fab5a2ba84
-- title:
--   Big B: S pos
-- statement:
--   The Big B construction uses the S pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/BigStatementPfB.lean#L23-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/BigStatementPfB.lean#L23-L45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PointwiseNormInvarianceHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModelNefness
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BigStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.ChartRestriction.G.AR.Up.BigB
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.BigB.S_pos (X : Data E r) (Xa : ArchInM X) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by sorry
