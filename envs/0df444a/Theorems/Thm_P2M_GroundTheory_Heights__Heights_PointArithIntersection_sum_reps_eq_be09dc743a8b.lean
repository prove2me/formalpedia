-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointArithIntersection_sum_reps_eq_be09dc743a8b
-- name    : P2M_GroundTheory_Heights__Heights_PointArithIntersection_sum_reps_eq_be09dc743a8b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:15:34.189587+00:00
-- url     : https://prove2.me/theorems/521398ff-2b6f-413e-9f6f-b94c22c87af9
-- title:
--   P2 M Ground Theory Heights  Heights Point Arith Intersection sum reps eq be09dc743a8b: P2 M Ground Theory Heights  Heights Point Arith Intersection sum reps eq be09dc743a8b
-- statement:
--   The P2 M Ground Theory Heights  Heights Point Arith Intersection sum reps eq be09dc743a8b construction uses the P2 M Ground Theory Heights  Heights Point Arith Intersection sum reps eq be09dc743a8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPointArInt.lean#L48-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPointArInt.lean#L48-L85

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

theorem P2M_GroundTheory_Heights__Heights_PointArithIntersection_sum_reps_eq_be09dc743a8b {y : (Σ _ : Unit, T) → K'} (hP : IsArithVar (mCoordIdeal y) 1) {c : Unit → T}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (R : Finset ((Σ _ : Unit, T) → ℂ))
    (hR : ∀ t ∈ R, t ∈ mcPts (mCoordIdeal y))
    (hU : ∀ z ∈ mcPts (mCoordIdeal y), ∃! t, t ∈ R ∧ SameOrbit z t)
    (F : ((Σ _ : Unit, T) → ℂ) → ℝ) (hF : ∀ t : ℂ, t ≠ 0 → ∀ z, F (fun p => t * z p) = F z)
    [Fintype (blockFnField y →ₐ[ℚ] ℂ)] :
    ∑ t ∈ R, F t = ∑ φ : blockFnField y →ₐ[ℚ] ℂ, F (ptOf y c φ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointArithIntersection».«sum_reps_eq» := P2M_GroundTheory_Heights__Heights_PointArithIntersection_sum_reps_eq_be09dc743a8b
