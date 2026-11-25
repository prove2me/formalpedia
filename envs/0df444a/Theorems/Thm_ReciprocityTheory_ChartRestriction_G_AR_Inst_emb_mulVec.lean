-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_emb_mulVec
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.emb_mulVec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:12:20.299674+00:00
-- url     : https://prove2.me/theorems/642efff6-f2a8-497d-b9ea-774aab834cc2
-- title:
--   Inst: emb mul Vec
-- statement:
--   The Inst construction uses the emb mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/FirstMinimumInvariantContinuousPos.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/FirstMinimumInvariantContinuousPos.lean#L25-L28

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PointwiseNormInvarianceHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MinimumGrowthBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMajorantFlags
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlagSpanBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_FirstMinimumInvariantContinuousPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.emb_mulVec (τ : E →+* ℂ) (M : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    (M.map τ) *ᵥ Data.emb τ v = Data.emb τ (M *ᵥ v) := by sorry
