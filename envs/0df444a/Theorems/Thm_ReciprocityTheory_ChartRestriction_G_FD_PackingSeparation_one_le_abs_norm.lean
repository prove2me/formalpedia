-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PackingSeparation_one_le_abs_norm
-- name    : ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation.one_le_abs_norm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:20:20.2729+00:00
-- url     : https://prove2.me/theorems/1348f8b0-926f-480f-bf78-6f7fecd10d13
-- title:
--   Packing Separation: one le abs norm
-- statement:
--   The Packing Separation construction uses the one le abs norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PackingSeparation.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PackingSeparation.lean#L58-L67

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralTraceNormBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PackingSeparation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation
open NumberField InfinitePlace Module MeasureTheory Metric TraceIntegralBasis IntegralTraceNormBounds
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation.one_le_abs_norm (γ : 𝓞 E) (hγ : γ ≠ 0) : 1 ≤ |(Algebra.norm ℚ (γ : E) : ℝ)| := by sorry
