-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralTraceNormBounds_cc_mul
-- name    : ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds.cc_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:18:29.350419+00:00
-- url     : https://prove2.me/theorems/99fb85bc-2376-5dc6-9653-1624f2f78d6f
-- title:
--   Integral Trace Norm Bounds: cc mul
-- statement:
--   The Integral Trace Norm Bounds construction uses the cc mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IntegralTraceNormBounds.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IntegralTraceNormBounds.lean#L10-L12

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

theorem ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds.cc_mul (a b : E) : cc (a * b) = cc a * cc b := by sorry
