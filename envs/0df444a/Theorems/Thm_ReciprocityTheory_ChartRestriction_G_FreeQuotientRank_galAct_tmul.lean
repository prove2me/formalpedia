-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_galAct_tmul
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.galAct_tmul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:22:10.541506+00:00
-- url     : https://prove2.me/theorems/89367c85-9306-574f-94e6-f1eaa7ec3a4e
-- title:
--   Free Quotient Rank: gal Act tmul
-- statement:
--   The Free Quotient Rank construction uses the gal Act tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FunKerPf.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FunKerPf.lean#L14-L15

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FunKerSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_RationalityHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FunKerPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_DescPf_galAct_tmul

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.galAct_tmul {K₂ : Type*} [Field K₂] [Algebra K K₂] (σ : K₂ ≃ₐ[K] K₂) (a : K₂) (v : V) :
    galAct σ (a ⊗ₜ[K] v) = σ a ⊗ₜ[K] v := by sorry
