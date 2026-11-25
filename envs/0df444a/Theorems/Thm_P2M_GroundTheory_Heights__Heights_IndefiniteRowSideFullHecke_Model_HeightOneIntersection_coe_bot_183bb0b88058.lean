-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_HeightOneIntersection_coe_bot_183bb0b88058
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_HeightOneIntersection_coe_bot_183bb0b88058
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:22:36.621796+00:00
-- url     : https://prove2.me/theorems/926bdc45-6ea8-46ff-8973-a16dca2689aa
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Height One Intersection coe bot 183bb0b88058: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Height O
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Height One Intersection coe bot 183bb0b88058 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Height One Intersection coe bot 183bb0b88058 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/EquivAt.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/EquivAt.lean#L12-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_EquivAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_HeightOneIntersection_coe_bot_183bb0b88058 :
    ((Subalgebra.toSubmodule (⊥ : Subalgebra A K) : Submodule A K) : Set K) =
      Set.range (algebraMap A K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«HeightOneIntersection».«coe_bot» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_HeightOneIntersection_coe_bot_183bb0b88058
