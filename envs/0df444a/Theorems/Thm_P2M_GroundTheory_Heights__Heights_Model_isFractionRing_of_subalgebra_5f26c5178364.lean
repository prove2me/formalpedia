-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isFractionRing_of_subalgebra_5f26c5178364
-- name    : P2M_GroundTheory_Heights__Heights_Model_isFractionRing_of_subalgebra_5f26c5178364
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:34.878592+00:00
-- url     : https://prove2.me/theorems/bcf93a46-fcd8-4d66-931e-09162b78ff0c
-- title:
--   P2 M Ground Theory Heights  Heights Model is Fraction Ring of subalgebra 5f26c5178364: P2 M Ground Theory Heights  Heights Model is Fraction Ring of subalgebra 5f26c5178364
-- statement:
--   The P2 M Ground Theory Heights  Heights Model is Fraction Ring of subalgebra 5f26c5178364 construction uses the P2 M Ground Theory Heights  Heights Model is Fraction Ring of subalgebra 5f26c5178364 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDominatingDVR.lean#L7-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDominatingDVR.lean#L7-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PDominatingDVR
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

theorem P2M_GroundTheory_Heights__Heights_Model_isFractionRing_of_subalgebra_5f26c5178364 {A K : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] (B : Subalgebra A K) : IsFractionRing B K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«isFractionRing_of_subalgebra» := P2M_GroundTheory_Heights__Heights_Model_isFractionRing_of_subalgebra_5f26c5178364
