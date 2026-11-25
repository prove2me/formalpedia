-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_lTensor_mkQ_galAct
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.lTensor_mkQ_galAct
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:23:18.324109+00:00
-- url     : https://prove2.me/theorems/3ff0d6ef-c8eb-44eb-9693-16dfe33e6323
-- title:
--   Free Quotient Rank: l Tensor mk Q gal Act
-- statement:
--   The Free Quotient Rank construction uses the l Tensor mk Q gal Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FunKerPf.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FunKerPf.lean#L17-L24

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.lTensor_mkQ_galAct {K₂ : Type*} [Field K₂] [Algebra K K₂] (U : Submodule K V)
    (σ : K₂ ≃ₐ[K] K₂) (x : K₂ ⊗[K] V) :
    LinearMap.lTensor K₂ U.mkQ (galAct σ x) =
      LinearMap.rTensor (V ⧸ U) σ.toLinearMap (LinearMap.lTensor K₂ U.mkQ x) := by sorry
