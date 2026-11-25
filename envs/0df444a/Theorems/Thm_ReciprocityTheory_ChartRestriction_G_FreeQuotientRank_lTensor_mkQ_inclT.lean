-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_lTensor_mkQ_inclT
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.lTensor_mkQ_inclT
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:28:38.932164+00:00
-- url     : https://prove2.me/theorems/fab8ed52-d1ff-4033-9e6e-f8832e2ce0e9
-- title:
--   Free Quotient Rank: l Tensor mk Q incl T
-- statement:
--   The Free Quotient Rank construction uses the l Tensor mk Q incl T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FiniteDimensionalBaseSpan.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FiniteDimensionalBaseSpan.lean#L56-L62

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.lTensor_mkQ_inclT (K₁ : IntermediateField K Ω) (U : Submodule K V) (x : K₁ ⊗[K] V) :
    LinearMap.lTensor Ω U.mkQ (inclT K₁ V x) =
      LinearMap.rTensor (V ⧸ U) (fldIncl K₁) (LinearMap.lTensor K₁ U.mkQ x) := by sorry
