-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionCycle_isHorizontal_imageZ_iff_1028b5244437
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionCycle_isHorizontal_imageZ_iff_1028b5244437
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:41:34.329597+00:00
-- url     : https://prove2.me/theorems/fa16cc4b-56a8-494b-86cb-0aa245f9f6b2
-- title:
--   P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Cycle is Horizontal image Z iff 1028b5244437: P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Cycle is Horizontal im
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Cycle is Horizontal image Z iff 1028b5244437 construction uses the P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Cycle is Horizontal image Z iff 1028b5244437 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHorizontalImageZIff.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHorizontalImageZIff.lean#L27-L29

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionCycle_isHorizontal_imageZ_iff_1028b5244437 (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) :
    IsHorizontal (imageZ v W') ↔ IsHorizontal W' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ArithmeticIntersectionCycle».«isHorizontal_imageZ_iff» := P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionCycle_isHorizontal_imageZ_iff_1028b5244437
