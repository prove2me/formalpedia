-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_iota_apply
-- name    : ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis.iota_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:54.636813+00:00
-- url     : https://prove2.me/theorems/c90d7b76-7055-4407-b751-fff5f9521fc1
-- title:
--   Trace Integral Basis: iota apply
-- statement:
--   The Trace Integral Basis construction uses the iota apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TraceIntegralBasis.lean#L24-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TraceIntegralBasis.lean#L24-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis
open NumberField InfinitePlace Module Submodule
open scoped ComplexConjugate Classical
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}

theorem ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis.iota_apply (x : E) (w : CP E) : iota E x w = w.1.embedding x := by sorry
