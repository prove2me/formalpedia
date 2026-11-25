-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralTraceNormBounds_trace_int
-- name    : ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds.trace_int
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:18:09.506429+00:00
-- url     : https://prove2.me/theorems/2978b9fd-0528-4ce9-9369-1747cf59a728
-- title:
--   Integral Trace Norm Bounds: trace int
-- statement:
--   The Integral Trace Norm Bounds construction uses the trace int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IntegralTraceNormBounds.lean#L50-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IntegralTraceNormBounds.lean#L50-L65

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

theorem ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds.trace_int (c : Free.ChooseBasisIndex ℤ (𝓞 E) → ℤ) (γ : 𝓞 E) :
    ∃ m : ℤ, Algebra.trace ℚ E ((∑ j, c j • ed E j) * (γ : E)) = m := by sorry
