-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjContract_finsum_mul_eq_sum_d96e0dfcb2b8
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjContract_finsum_mul_eq_sum_d96e0dfcb2b8
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:06:25.793728+00:00
-- url     : https://prove2.me/theorems/384f9b14-9376-414c-95c4-68d9d1633384
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Contract finsum mul eq sum d96e0dfcb2b8: P2 M Ground Theory Heights  Heights Targets Proj Contract finsum mul eq sum d96e0dfcb2b8
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Contract finsum mul eq sum d96e0dfcb2b8 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Contract finsum mul eq sum d96e0dfcb2b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ProjContract.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ProjContract.lean#L19-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_BlockInclInjectiveOfEmbedding
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ProjContract
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Targets.ProjContract

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjContract_finsum_mul_eq_sum_d96e0dfcb2b8 {α : Type*} (D : α →₀ ℤ) (J : α → ℤ) :
    ∑ᶠ W, D W * J W = D.sum fun W m => m * J W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjContract».«finsum_mul_eq_sum» := P2M_GroundTheory_Heights__Heights_Targets_ProjContract_finsum_mul_eq_sum_d96e0dfcb2b8
