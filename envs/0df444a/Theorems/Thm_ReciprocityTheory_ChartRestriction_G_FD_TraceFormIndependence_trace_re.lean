-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceFormIndependence_trace_re
-- name    : ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence.trace_re
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:11:32.062906+00:00
-- url     : https://prove2.me/theorems/848f4eeb-216d-472f-bfc3-45c489d98c51
-- title:
--   Trace Form Independence: trace re
-- statement:
--   The Trace Form Independence construction uses the trace re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TraceFormIndependence.lean#L16-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TraceFormIndependence.lean#L16-L47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceFormIndependence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence.trace_re (X : Data E r) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ : X.Ψ, 2 * (τ.1 z).re := by sorry
