-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_galAct_mem_baseSpan
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.galAct_mem_baseSpan
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:22:14.780104+00:00
-- url     : https://prove2.me/theorems/8f750448-b9c9-5f28-ab41-490453ee3ca8
-- title:
--   Free Quotient Rank: gal Act mem base Span
-- statement:
--   The Free Quotient Rank construction uses the gal Act mem base Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FunKerPf.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FunKerPf.lean#L26-L29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FunKerSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_RationalityHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FunKerPf
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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.galAct_mem_baseSpan {K₂ : Type*} [Field K₂] [Algebra K K₂] (U : Submodule K V)
    (σ : K₂ ≃ₐ[K] K₂) {x : K₂ ⊗[K] V} (hx : x ∈ baseSpan K₂ U) : galAct σ x ∈ baseSpan K₂ U := by sorry
