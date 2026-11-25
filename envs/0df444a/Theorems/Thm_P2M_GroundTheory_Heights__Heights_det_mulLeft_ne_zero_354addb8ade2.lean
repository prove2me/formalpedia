-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_mulLeft_ne_zero_354addb8ade2
-- name    : P2M_GroundTheory_Heights__Heights_det_mulLeft_ne_zero_354addb8ade2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:31.329205+00:00
-- url     : https://prove2.me/theorems/8d8f38eb-2a12-4a2f-ad1b-e56496d98a71
-- title:
--   P2 M Ground Theory Heights  Heights det mul Left ne zero 354addb8ade2: P2 M Ground Theory Heights  Heights det mul Left ne zero 354addb8ade2
-- statement:
--   The P2 M Ground Theory Heights  Heights det mul Left ne zero 354addb8ade2 construction uses the P2 M Ground Theory Heights  Heights det mul Left ne zero 354addb8ade2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PSpecFirstNe.lean#L55-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PSpecFirstNe.lean#L55-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PSpecFirstNe
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
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_det_mulLeft_ne_zero_354addb8ade2 {O B : Type*} [CommRing O] [IsDomain O] [CommRing B] [IsDomain B] [Algebra O B]
    {θ : B} (hθ : θ ≠ 0) : LinearMap.det (LinearMap.mulLeft O θ) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«det_mulLeft_ne_zero» := P2M_GroundTheory_Heights__Heights_det_mulLeft_ne_zero_354addb8ade2
