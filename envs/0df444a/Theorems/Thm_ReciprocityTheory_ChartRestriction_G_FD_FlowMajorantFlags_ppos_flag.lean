-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMajorantFlags_ppos_flag
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags.ppos_flag
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:14:24.642911+00:00
-- url     : https://prove2.me/theorems/0ee2083f-3e54-5312-b93a-41339aef88e4
-- title:
--   Flow Majorant Flags: ppos flag
-- statement:
--   The Flow Majorant Flags construction uses the ppos flag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMajorantFlags.lean#L31-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMajorantFlags.lean#L31-L50

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMajorantFlags
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags.ppos_flag {z z' : Frame X.Ψ r} (hz : z ∈ X.dom) (hz' : z' ∈ X.dom) (hf : X.SameFlag z z')
    (τ : X.Ψ) (v : Fin r → ℂ) : X.ppos z' τ v = X.ppos z τ v := by sorry
