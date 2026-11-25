-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_mem_baseSpan_of_inclT
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.mem_baseSpan_of_inclT
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:29:03.185852+00:00
-- url     : https://prove2.me/theorems/aadd6b55-1875-4e3f-9b63-ec96d7fb0824
-- title:
--   Free Quotient Rank: mem base Span of incl T
-- statement:
--   The Free Quotient Rank construction uses the mem base Span of incl T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FiniteDimensionalBaseSpan.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FiniteDimensionalBaseSpan.lean#L64-L69

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.mem_baseSpan_of_inclT (K₁ : IntermediateField K Ω) (U : Submodule K V) (x : K₁ ⊗[K] V)
    (h : inclT K₁ V x ∈ baseSpan Ω U) : x ∈ baseSpan K₁ U := by sorry
