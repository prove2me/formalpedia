-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMajorantFlags_ppos_flowV
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags.ppos_flowV
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:17:39.230182+00:00
-- url     : https://prove2.me/theorems/ea709967-8b68-4170-909f-001443eb8915
-- title:
--   Flow Majorant Flags: ppos flow V
-- statement:
--   The Flow Majorant Flags construction uses the ppos flow V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMajorantFlags.lean#L73-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMajorantFlags.lean#L73-L101

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

theorem ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags.ppos_flowV (e : X.Ψ → Fin r → ℂ) (s : X.Ψ → ℂ) {z : Frame X.Ψ r} (hz : z ∈ X.dom)
    (hTz : X.flowV e s z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ)
    (hve : hermC τ.1 X.Gm v (e τ) = 0) (hpe : hermC τ.1 X.Gm (X.ppos z τ v) (e τ) = 0) :
    X.ppos (X.flowV e s z) τ v = X.ppos z τ v := by sorry
