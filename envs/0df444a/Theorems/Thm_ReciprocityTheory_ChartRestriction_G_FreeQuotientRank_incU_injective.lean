-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_incU_injective
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.incU_injective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:22:39.114588+00:00
-- url     : https://prove2.me/theorems/b76ca243-95d3-5089-b9ce-ef9390f02fc1
-- title:
--   Free Quotient Rank: inc U injective
-- statement:
--   The Free Quotient Rank construction uses the inc U injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FiniteDimensionalBaseSpan.lean#L105-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FiniteDimensionalBaseSpan.lean#L105-L109

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.incU_injective (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    Function.Injective (incU F U) := by sorry
