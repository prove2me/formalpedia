-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesLineDegree_genIndex_map_of_injective_818d1ee55c6c
-- name    : P2M_GroundTheory_Heights__Heights_KLinesLineDegree_genIndex_map_of_injective_818d1ee55c6c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:07.04048+00:00
-- url     : https://prove2.me/theorems/14578cd6-a95f-4d07-a3ab-76b2e60b8ce6
-- title:
--   P2 M Ground Theory Heights  Heights KLines Line Degree gen Index map of injective 818d1ee55c6c: P2 M Ground Theory Heights  Heights KLines Line Degree gen Index map of injective 818d1ee55c6c
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Line Degree gen Index map of injective 818d1ee55c6c construction uses the P2 M Ground Theory Heights  Heights KLines Line Degree gen Index map of injective 818d1ee55c6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesLineDegree.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesLineDegree.lean#L16-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesLineDegree
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
open NumberField Matrix
open scoped nonZeroDivisors
noncomputable section
open GroundTheory.Heights₂.Heights.KLinesLineDegree
variable {K : Type} [Field K] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_KLinesLineDegree_genIndex_map_of_injective_818d1ee55c6c {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G →+ G')
    (hf : Function.Injective f) (A B : AddSubgroup G) :
    genIndex (A.map f) (B.map f) = genIndex A B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesLineDegree».«genIndex_map_of_injective» := P2M_GroundTheory_Heights__Heights_KLinesLineDegree_genIndex_map_of_injective_818d1ee55c6c
