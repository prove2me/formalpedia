-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointArithIntersection_eq_of_ptOf_eq_smul_c4234cca63a4
-- name    : P2M_GroundTheory_Heights__Heights_PointArithIntersection_eq_of_ptOf_eq_smul_c4234cca63a4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:16:08.939802+00:00
-- url     : https://prove2.me/theorems/494ee460-a858-4acd-baa1-43d025f2d0f1
-- title:
--   P2 M Ground Theory Heights  Heights Point Arith Intersection eq of pt Of eq smul c4234cca63a4: P2 M Ground Theory Heights  Heights Point Arith Intersection eq of pt Of eq smul c4234cca63a4
-- statement:
--   The P2 M Ground Theory Heights  Heights Point Arith Intersection eq of pt Of eq smul c4234cca63a4 construction uses the P2 M Ground Theory Heights  Heights Point Arith Intersection eq of pt Of eq smul c4234cca63a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPointArInt.lean#L35-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPointArInt.lean#L35-L46

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

theorem P2M_GroundTheory_Heights__Heights_PointArithIntersection_eq_of_ptOf_eq_smul_c4234cca63a4 {y : (Σ _ : Unit, T) → K'} {c : Unit → T} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {φ ψ : blockFnField y →ₐ[ℚ] ℂ} (t : ℂ) (h : ptOf y c φ = fun p => t * ptOf y c ψ p) : φ = ψ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointArithIntersection».«eq_of_ptOf_eq_smul» := P2M_GroundTheory_Heights__Heights_PointArithIntersection_eq_of_ptOf_eq_smul_c4234cca63a4
