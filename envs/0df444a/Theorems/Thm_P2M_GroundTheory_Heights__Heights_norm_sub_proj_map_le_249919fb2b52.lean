-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_norm_sub_proj_map_le_249919fb2b52
-- name    : P2M_GroundTheory_Heights__Heights_norm_sub_proj_map_le_249919fb2b52
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:49:13.170215+00:00
-- url     : https://prove2.me/theorems/2d194dc3-3687-4270-a99b-93bd55fe8036
-- title:
--   P2 M Ground Theory Heights  Heights norm sub proj map le 249919fb2b52: P2 M Ground Theory Heights  Heights norm sub proj map le 249919fb2b52
-- statement:
--   The P2 M Ground Theory Heights  Heights norm sub proj map le 249919fb2b52 construction uses the P2 M Ground Theory Heights  Heights norm sub proj map le 249919fb2b52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean#L93-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean#L93-L111

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
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
open Matrix
open scoped ComplexOrder
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem P2M_GroundTheory_Heights__Heights_norm_sub_proj_map_le_249919fb2b52 {ι : Type*} [Fintype ι] (Y : Submodule ℂ V) [Y.HasOrthogonalProjection]
    (c : ι → V) (x : V) :
    ‖Y.starProjection x - (Submodule.span ℂ (Set.range fun i ↦ Y.starProjection (c i))).starProjection
        (Y.starProjection x)‖ ≤ ‖x - (Submodule.span ℂ (Set.range c)).starProjection x‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«norm_sub_proj_map_le» := P2M_GroundTheory_Heights__Heights_norm_sub_proj_map_le_249919fb2b52
