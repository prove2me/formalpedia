-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionCycle_proof_66fb8ab5357f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionCycle_proof_66fb8ab5357f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:47.371392+00:00
-- url     : https://prove2.me/theorems/f140db17-ede1-40a0-951a-ff3acb57d9c4
-- title:
--   P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Cycle proof 66fb8ab5357f: P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Cycle proof 66fb8ab5357f
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Cycle proof 66fb8ab5357f construction uses the P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Cycle proof 66fb8ab5357f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHorizontalImageZIff.lean#L38-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHorizontalImageZIff.lean#L38-L131

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsPrimeSpanXb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalSpanXb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalSpanTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IdDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalImageZIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionCycle_proof_66fb8ab5357f (hHor : ArithmeticIntersectionHorizontal.Statement) (hVert : ArithmeticIntersectionVertical.Statement) (hPush : ArithmeticIntersectionDivisorPushforward.Statement)
    (hGP : GenericPointExists.Statement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι) :
    ArithmeticIntersectionCycle.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ArithmeticIntersectionCycle».«proof» := P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionCycle_proof_66fb8ab5357f
