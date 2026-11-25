-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlaceCentredSum_neg_log_apply_dfa8e9f4105e
-- name    : P2M_GroundTheory_Heights__Heights_PlaceCentredSum_neg_log_apply_dfa8e9f4105e
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:15:59.008156+00:00
-- url     : https://prove2.me/theorems/22e5ed99-8579-4d9b-82a1-5edd198fd8fe
-- title:
--   P2 M Ground Theory Heights  Heights Place Centred Sum neg log apply dfa8e9f4105e: P2 M Ground Theory Heights  Heights Place Centred Sum neg log apply dfa8e9f4105e
-- statement:
--   The P2 M Ground Theory Heights  Heights Place Centred Sum neg log apply dfa8e9f4105e construction uses the P2 M Ground Theory Heights  Heights Place Centred Sum neg log apply dfa8e9f4105e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPlaceCentredSum.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPlaceCentredSum.lean#L65-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlaceCentredSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPlaceCentredSum
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
open NumberField IsDedekindDomain Ideal
open GroundTheory.Heights₂.Heights.PlaceCentredSum
variable {L K : Type} [Field L] [NumberField L] [Field K] [NumberField K] [Algebra L K]

theorem P2M_GroundTheory_Heights__Heights_PlaceCentredSum_neg_log_apply_dfa8e9f4105e (v : FinitePlace K) (t : L) :
    -Real.log (v (algebraMap L K t)) = deg L v * -Real.log (FinitePlace.mk (below v) t) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PlaceCentredSum».«neg_log_apply» := P2M_GroundTheory_Heights__Heights_PlaceCentredSum_neg_log_apply_dfa8e9f4105e
