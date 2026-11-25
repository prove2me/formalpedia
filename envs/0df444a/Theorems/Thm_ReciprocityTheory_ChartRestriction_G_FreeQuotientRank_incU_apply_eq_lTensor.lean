-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_incU_apply_eq_lTensor
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.incU_apply_eq_lTensor
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:28:45.454796+00:00
-- url     : https://prove2.me/theorems/f5355137-107a-4a2a-a6c9-590753e68524
-- title:
--   Free Quotient Rank: inc U apply eq l Tensor
-- statement:
--   The Free Quotient Rank construction uses the inc U apply eq l Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FiniteDimensionalBaseSpan.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FiniteDimensionalBaseSpan.lean#L14-L19

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.incU_apply_eq_lTensor (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    (y : F ⊗[K] U) : incU F U y = LinearMap.lTensor F U.subtype y := by sorry
