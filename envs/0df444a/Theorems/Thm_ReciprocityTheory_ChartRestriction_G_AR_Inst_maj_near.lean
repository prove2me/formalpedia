-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_maj_near
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.maj_near
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:12:23.868884+00:00
-- url     : https://prove2.me/theorems/f4570b74-f6a0-4bd0-aa6a-af1b881a46b3
-- title:
--   Inst: maj near
-- statement:
--   The Inst construction uses the maj near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/FirstMinimumInvariantContinuousPos.lean#L113-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/FirstMinimumInvariantContinuousPos.lean#L113-L148

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
open Topology Filter

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.maj_near (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom) {κ : ℝ} (hκ : 1 < κ) :
    ∀ᶠ w in 𝓝 x0, w ∈ X.dom → ∀ τ v, κ⁻¹ * X.maj x0 τ v ≤ X.maj w τ v ∧ X.maj w τ v ≤ κ * X.maj x0 τ v := by sorry
