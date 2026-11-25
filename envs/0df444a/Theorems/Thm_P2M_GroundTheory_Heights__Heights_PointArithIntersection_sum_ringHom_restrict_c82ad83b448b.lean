-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointArithIntersection_sum_ringHom_restrict_c82ad83b448b
-- name    : P2M_GroundTheory_Heights__Heights_PointArithIntersection_sum_ringHom_restrict_c82ad83b448b
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:15:48.22562+00:00
-- url     : https://prove2.me/theorems/a518e1fd-7d5f-4a33-a6a2-1a53eef0bfc3
-- title:
--   P2 M Ground Theory Heights  Heights Point Arith Intersection sum ring Hom restrict c82ad83b448b: P2 M Ground Theory Heights  Heights Point Arith Intersection sum ring Hom restrict c82ad83b448b
-- statement:
--   The P2 M Ground Theory Heights  Heights Point Arith Intersection sum ring Hom restrict c82ad83b448b construction uses the P2 M Ground Theory Heights  Heights Point Arith Intersection sum ring Hom restrict c82ad83b448b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPointArInt.lean#L87-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPointArInt.lean#L87-L106

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIsSheetFinZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPointArInt
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.PointArithIntersection
open IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
variable {T : Type} [Fintype T]
variable {K' : Type} [Field K'] [NumberField K']

theorem P2M_GroundTheory_Heights__Heights_PointArithIntersection_sum_ringHom_restrict_c82ad83b448b (κ : IntermediateField ℚ K') (H : (κ →ₐ[ℚ] ℂ) → ℝ)
    [Fintype (κ →ₐ[ℚ] ℂ)] :
    ∑ σ : K' →+* ℂ, H ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K')) =
      (Module.finrank κ K' : ℝ) * ∑ f, H f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointArithIntersection».«sum_ringHom_restrict» := P2M_GroundTheory_Heights__Heights_PointArithIntersection_sum_ringHom_restrict_c82ad83b448b
