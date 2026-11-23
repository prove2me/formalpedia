-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralTraceNormBounds_trace_ed
-- name    : ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds.trace_ed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:50.502663+00:00
-- url     : https://prove2.me/theorems/e871a581-e9bc-45c6-87fc-b77ed0018edd
-- title:
--   Integral Trace Norm Bounds: trace ed
-- statement:
--   The Integral Trace Norm Bounds construction uses the trace ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IntegralTraceNormBounds.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IntegralTraceNormBounds.lean#L32-L35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralTraceNormBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds
open NumberField InfinitePlace Module Submodule TraceIntegralBasis
open scoped ComplexConjugate Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds.trace_ed (i j : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E (integralBasis E i * ed E j) = if i = j then 1 else 0 := by sorry
