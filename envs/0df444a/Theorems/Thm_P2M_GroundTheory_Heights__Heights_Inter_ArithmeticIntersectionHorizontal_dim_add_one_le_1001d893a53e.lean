-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_dim_add_one_le_1001d893a53e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_dim_add_one_le_1001d893a53e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:40:46.401834+00:00
-- url     : https://prove2.me/theorems/20cc0d49-7362-472a-897a-9ac3409e4c1b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal dim add one le 1001d893a53e: P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal dim add one le 10
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal dim add one le 1001d893a53e construction uses the P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal dim add one le 1001d893a53e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHorizontalImageZ.lean#L31-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHorizontalImageZ.lean#L31-L43

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_dim_add_one_le_1001d893a53e {R : Type*} [CommRing R] {Q Q₂ : Ideal R} [Q.IsPrime] (hle : Q ≤ Q₂)
    {x : R} (hx : x ∈ Q₂) (hxQ : x ∉ Q) : ringKrullDim (R ⧸ Q₂) + 1 ≤ ringKrullDim (R ⧸ Q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ArithmeticIntersectionHorizontal».«dim_add_one_le» := P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_dim_add_one_le_1001d893a53e
