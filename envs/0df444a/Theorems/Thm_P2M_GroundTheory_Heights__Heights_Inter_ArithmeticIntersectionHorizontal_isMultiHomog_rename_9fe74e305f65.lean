-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_isMultiHomog_rename_9fe74e305f65
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_isMultiHomog_rename_9fe74e305f65
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:50.59485+00:00
-- url     : https://prove2.me/theorems/4b87df50-0eaf-49f1-ab8d-911e95325018
-- title:
--   P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal is Multi Homog rename 9fe74e305f65: P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal is Multi H
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal is Multi Homog rename 9fe74e305f65 construction uses the P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal is Multi Homog rename 9fe74e305f65 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHorizontalImageZ.lean#L85-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHorizontalImageZ.lean#L85-L115

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_isMultiHomog_rename_9fe74e305f65 {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {s : MRing ι} {α : K → ℕ} (hs : IsMultiHomog s α) :
    IsMultiHomog (rename v s) (Function.extend κ α 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ArithmeticIntersectionHorizontal».«isMultiHomog_rename» := P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_isMultiHomog_rename_9fe74e305f65
