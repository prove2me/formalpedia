-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_dim_eq_a8c8db789c89
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_dim_eq_a8c8db789c89
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:41:23.746009+00:00
-- url     : https://prove2.me/theorems/e7bd83a5-187d-4d05-8aca-eecdfd3353cf
-- title:
--   P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal dim eq a8c8db789c89: P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal dim eq a8c8db789c89
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal dim eq a8c8db789c89 construction uses the P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal dim eq a8c8db789c89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHorizontalImageZ.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHorizontalImageZ.lean#L26-L29

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_dim_eq_a8c8db789c89 {P : Ideal (MRing ι)} {d d' : ℕ} (h : IsArithVar P d) (h' : IsArithVar P d') : d = d' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ArithmeticIntersectionHorizontal».«dim_eq» := P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_dim_eq_a8c8db789c89
