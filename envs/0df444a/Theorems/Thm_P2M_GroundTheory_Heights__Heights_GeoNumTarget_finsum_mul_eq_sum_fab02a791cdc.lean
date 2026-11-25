-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GeoNumTarget_finsum_mul_eq_sum_fab02a791cdc
-- name    : P2M_GroundTheory_Heights__Heights_GeoNumTarget_finsum_mul_eq_sum_fab02a791cdc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:00:39.554666+00:00
-- url     : https://prove2.me/theorems/7a93bc4d-e167-5250-9493-dabbbb38990e
-- title:
--   P2 M Ground Theory Heights  Heights Geo Num Target finsum mul eq sum fab02a791cdc: P2 M Ground Theory Heights  Heights Geo Num Target finsum mul eq sum fab02a791cdc
-- statement:
--   The P2 M Ground Theory Heights  Heights Geo Num Target finsum mul eq sum fab02a791cdc construction uses the P2 M Ground Theory Heights  Heights Geo Num Target finsum mul eq sum fab02a791cdc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GeoNum.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GeoNum.lean#L27-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_GeoNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyBridgeFull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GeoNum
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
open GroundTheory.Heights₂.Heights.GeoNumTarget
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_GeoNumTarget_finsum_mul_eq_sum_fab02a791cdc {α : Type*} (D : α →₀ ℤ) (J : α → ℤ) :
    ∑ᶠ W, D W * J W = D.sum fun W m => m * J W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GeoNumTarget».«finsum_mul_eq_sum» := P2M_GroundTheory_Heights__Heights_GeoNumTarget_finsum_mul_eq_sum_fab02a791cdc
