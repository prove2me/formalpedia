-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_map_injective_fc941090a98a
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_map_injective_fc941090a98a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:54.950685+00:00
-- url     : https://prove2.me/theorems/34d74c1b-0c7c-449c-986e-618dc7123dd7
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers rel Dim map injective fc941090a98a: P2 M Ground Theory Heights  Heights Field Numbers rel Dim map injective fc941090a98a
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers rel Dim map injective fc941090a98a construction uses the P2 M Ground Theory Heights  Heights Field Numbers rel Dim map injective fc941090a98a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDivPrincipalDegree.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDivPrincipalDegree.lean#L29-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDivPrincipalDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open GroundTheory.Heights₂.Heights.NumbersDVR
universe u
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]
omit [DecidableEq K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_map_injective_fc941090a98a :
    Function.Injective (WithBot.map (fun d : ℕ∞ =>
      WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«relDim_map_injective» := P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_map_injective_fc941090a98a
