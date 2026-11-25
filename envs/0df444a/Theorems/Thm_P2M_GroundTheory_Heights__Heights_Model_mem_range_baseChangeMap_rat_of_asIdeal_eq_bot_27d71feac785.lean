-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_range_baseChangeMap_rat_of_asIdeal_eq_bot_27d71feac785
-- name    : P2M_GroundTheory_Heights__Heights_Model_mem_range_baseChangeMap_rat_of_asIdeal_eq_bot_27d71feac785
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:34.258844+00:00
-- url     : https://prove2.me/theorems/5cb9f1c9-bc6d-429d-98e7-e3445dd8ba95
-- title:
--   P2 M Ground Theory Heights  Heights Model mem range base Change Map rat of as Ideal eq bot 27d71feac785: P2 M Ground Theory Heights  Heights Model mem range base Change Map rat of as Ideal eq bot 27d7
-- statement:
--   The P2 M Ground Theory Heights  Heights Model mem range base Change Map rat of as Ideal eq bot 27d71feac785 construction uses the P2 M Ground Theory Heights  Heights Model mem range base Change Map rat of as Ideal eq bot 27d71feac785 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PInvOpenInsideRat.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PInvOpenInsideRat.lean#L23-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsInvOpenInsideRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PInvOpenInsideRat
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

theorem P2M_GroundTheory_Heights__Heights_Model_mem_range_baseChangeMap_rat_of_asIdeal_eq_bot_27d71feac785 {X : Scheme.{0}} (f : X ⟶ SpecZ) (x : X)
    (hx : (f.base x).asIdeal = ⊥) : x ∈ Set.range (baseChangeMap f ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«mem_range_baseChangeMap_rat_of_asIdeal_eq_bot» := P2M_GroundTheory_Heights__Heights_Model_mem_range_baseChangeMap_rat_of_asIdeal_eq_bot_27d71feac785
