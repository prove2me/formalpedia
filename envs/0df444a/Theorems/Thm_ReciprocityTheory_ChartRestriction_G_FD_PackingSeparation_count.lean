-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PackingSeparation_count
-- name    : ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation.count
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:13.52085+00:00
-- url     : https://prove2.me/theorems/b710e5ce-da52-4da1-8582-2d9f2bfb13c6
-- title:
--   Packing Separation: count
-- statement:
--   The Packing Separation construction uses the count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PackingSeparation.lean#L84-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PackingSeparation.lean#L84-L120

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

theorem ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation.count (R : ℝ) (hR : 0 ≤ R) :
    {α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}.Finite ∧
      ({α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}.ncard : ℝ) ≤ (1 + 2 * R) ^ (2 * fdeg E) := by sorry
