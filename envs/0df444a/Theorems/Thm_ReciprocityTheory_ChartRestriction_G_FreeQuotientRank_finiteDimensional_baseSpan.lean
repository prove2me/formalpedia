-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_finiteDimensional_baseSpan
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.finiteDimensional_baseSpan
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:28:53.787482+00:00
-- url     : https://prove2.me/theorems/9203638e-f50f-4003-a382-05dd9fa1514d
-- title:
--   Free Quotient Rank: finite Dimensional base Span
-- statement:
--   The Free Quotient Rank construction uses the finite Dimensional base Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FiniteDimensionalBaseSpan.lean#L116-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FiniteDimensionalBaseSpan.lean#L116-L118

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.finiteDimensional_baseSpan (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    [FiniteDimensional K U] : FiniteDimensional F (baseSpan F U) := by sorry
