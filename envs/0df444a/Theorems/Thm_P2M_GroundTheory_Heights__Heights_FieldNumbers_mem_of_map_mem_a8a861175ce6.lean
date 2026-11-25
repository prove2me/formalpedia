-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_of_map_mem_a8a861175ce6
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_of_map_mem_a8a861175ce6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:51.893117+00:00
-- url     : https://prove2.me/theorems/67415a91-4ac7-4ffd-953a-a14d36d4cb09
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers mem of map mem a8a861175ce6: P2 M Ground Theory Heights  Heights Field Numbers mem of map mem a8a861175ce6
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers mem of map mem a8a861175ce6 construction uses the P2 M Ground Theory Heights  Heights Field Numbers mem of map mem a8a861175ce6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L96-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L96-L100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {σ : Type*} {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_of_map_mem_a8a861175ce6 {I : Ideal (MvPolynomial σ F)} {g : MvPolynomial σ F}
    (h : map (algebraMap F F') g ∈ I.map (map (algebraMap F F'))) : g ∈ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«mem_of_map_mem» := P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_of_map_mem_a8a861175ce6
