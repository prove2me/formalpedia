-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_inner_iota
-- name    : ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis.inner_iota
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:22:01.045803+00:00
-- url     : https://prove2.me/theorems/15e13ed3-46b3-5fbc-9bab-b1b5ac50efeb
-- title:
--   Trace Integral Basis: inner iota
-- statement:
--   The Trace Integral Basis construction uses the inner iota property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TraceIntegralBasis.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TraceIntegralBasis.lean#L40-L46

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

theorem ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis.inner_iota (x y : E) :
    inner ℝ (iota E x) (iota E y) = ∑ w : CP E, (w.1.embedding x * conj (w.1.embedding y)).re := by sorry
