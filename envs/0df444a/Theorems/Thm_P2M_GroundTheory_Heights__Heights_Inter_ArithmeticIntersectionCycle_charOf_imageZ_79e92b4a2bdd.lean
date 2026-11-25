-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionCycle_charOf_imageZ_79e92b4a2bdd
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionCycle_charOf_imageZ_79e92b4a2bdd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:41:41.07026+00:00
-- url     : https://prove2.me/theorems/e0ba4738-1515-4e79-a791-4704d2f06572
-- title:
--   P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Cycle char Of image Z 79e92b4a2bdd: P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Cycle char Of image Z 79e92b4a2b
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Cycle char Of image Z 79e92b4a2bdd construction uses the P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Cycle char Of image Z 79e92b4a2bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHorizontalImageZIff.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHorizontalImageZIff.lean#L32-L34

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
open GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionCycle
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionCycle_charOf_imageZ_79e92b4a2bdd (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) :
    charOf (imageZ v W') = charOf W' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ArithmeticIntersectionCycle».«charOf_imageZ» := P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionCycle_charOf_imageZ_79e92b4a2bdd
