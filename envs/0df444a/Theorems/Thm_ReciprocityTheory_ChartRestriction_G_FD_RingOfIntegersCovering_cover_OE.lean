-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RingOfIntegersCovering_cover_OE
-- name    : ReciprocityTheory.ChartRestriction.G.FD.RingOfIntegersCovering.cover_OE
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:14.851821+00:00
-- url     : https://prove2.me/theorems/0aa54fcb-af17-57ab-afcd-b9cf55ee95f4
-- title:
--   Ring Of Integers Covering: cover OE
-- statement:
--   The Ring Of Integers Covering construction uses the cover OE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RingOfIntegersCovering.lean#L11-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RingOfIntegersCovering.lean#L11-L57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BabaiCovering
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralTraceNormBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RingOfIntegersCovering
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.RingOfIntegersCovering
open NumberField InfinitePlace Module Submodule TraceIntegralBasis IntegralTraceNormBounds
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.RingOfIntegersCovering.cover_OE (Z : VS E) :
    ∃ α : 𝓞 E, ‖Z - iota E (α : E)‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := by sorry
