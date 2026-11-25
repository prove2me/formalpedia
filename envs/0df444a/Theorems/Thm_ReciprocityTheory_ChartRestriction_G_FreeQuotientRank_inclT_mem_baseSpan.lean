-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_inclT_mem_baseSpan
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.inclT_mem_baseSpan
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:28:24.594799+00:00
-- url     : https://prove2.me/theorems/ce5112eb-7ec9-4de2-be99-bf628e1e293f
-- title:
--   Free Quotient Rank: incl T mem base Span
-- statement:
--   The Free Quotient Rank construction uses the incl T mem base Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FiniteDimensionalBaseSpan.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FiniteDimensionalBaseSpan.lean#L71-L74

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDetectStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDimensionalBaseSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
open TensorProduct
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {Ω : Type*} [Field Ω] [Algebra K Ω]

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.inclT_mem_baseSpan (K₁ : IntermediateField K Ω) (U : Submodule K V) (x : K₁ ⊗[K] V)
    (h : x ∈ baseSpan K₁ U) : inclT K₁ V x ∈ baseSpan Ω U := by sorry
