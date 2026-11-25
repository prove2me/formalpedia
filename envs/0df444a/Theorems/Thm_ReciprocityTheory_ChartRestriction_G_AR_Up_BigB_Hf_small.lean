-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_BigB_Hf_small
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.BigB.Hf_small
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T15:11:29.772623+00:00
-- url     : https://prove2.me/theorems/ecd491f3-2f88-4c91-bbde-2c3ef3dc12de
-- title:
--   Big B: Hf small
-- statement:
--   The Big B construction uses the Hf small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/BigStatementPfB.lean#L351-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/BigStatementPfB.lean#L351-L454

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.BigB.Hf_small (X : Data E r) (Xa : ArchInM X) {h1 : ℝ} (hh1 : 0 < h1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ X.dom, X.la1 x < ε → Hf X Xa x < h1 := by sorry
