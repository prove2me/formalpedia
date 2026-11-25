-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_isHorizontal_imageZ_419052dac111
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_isHorizontal_imageZ_419052dac111
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:41:21.853786+00:00
-- url     : https://prove2.me/theorems/74d9dc5d-bc5b-4583-90ef-ad6fc07d4ae7
-- title:
--   P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal is Horizontal image Z 419052dac111: P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal is Horizon
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal is Horizontal image Z 419052dac111 construction uses the P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal is Horizontal image Z 419052dac111 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHorizontalImageZ.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHorizontalImageZ.lean#L18-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalSpanXb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalImageZ
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
open GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_isHorizontal_imageZ_419052dac111 {v : (Σ k, ι k) → (Σ k', ι' k')} {W' : Ideal (MRing ι')} (h : IsHorizontal W') :
    IsHorizontal (imageZ v W') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ArithmeticIntersectionHorizontal».«isHorizontal_imageZ» := P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_isHorizontal_imageZ_419052dac111
