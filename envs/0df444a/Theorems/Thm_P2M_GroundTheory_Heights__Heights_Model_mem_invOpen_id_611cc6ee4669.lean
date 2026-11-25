-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_invOpen_id_611cc6ee4669
-- name    : P2M_GroundTheory_Heights__Heights_Model_mem_invOpen_id_611cc6ee4669
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:31:46.484002+00:00
-- url     : https://prove2.me/theorems/46601d02-530a-4c7c-bb3d-834fba323da4
-- title:
--   P2 M Ground Theory Heights  Heights Model mem inv Open id 611cc6ee4669: P2 M Ground Theory Heights  Heights Model mem inv Open id 611cc6ee4669
-- statement:
--   The P2 M Ground Theory Heights  Heights Model mem inv Open id 611cc6ee4669 construction uses the P2 M Ground Theory Heights  Heights Model mem inv Open id 611cc6ee4669 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsGlue.lean#L35-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsGlue.lean#L35-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Model_mem_invOpen_id_611cc6ee4669 (m : ℤ) (x : SpecZ) : x ∈ invOpen (𝟙 SpecZ) m ↔ m ∉ x.asIdeal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«mem_invOpen_id» := P2M_GroundTheory_Heights__Heights_Model_mem_invOpen_id_611cc6ee4669
