-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_exists_ratFun
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.exists_ratFun
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:29:10.204941+00:00
-- url     : https://prove2.me/theorems/1042902d-5357-4b44-aea2-50d82bf6e2fb
-- title:
--   Free Quotient Rank: exists rat Fun
-- statement:
--   The Free Quotient Rank construction uses the exists rat Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FiniteDimensionalBaseSpan.lean#L120-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FiniteDimensionalBaseSpan.lean#L120-L130

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.exists_ratFun {c : Module.Dual Ω (Ω ⊗[K] V)} {K₁ : IntermediateField K Ω}
    (h : DefinedOver c K₁) :
    ∃ φ : Module.Dual K₁ (K₁ ⊗[K] V), ∀ x, algebraMap K₁ Ω (φ x) = c (inclT K₁ V x) := by sorry
