-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ClaimVanish_proof_dce3cf61647f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ClaimVanish_proof_dce3cf61647f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:39:17.202216+00:00
-- url     : https://prove2.me/theorems/f7cd13fd-c027-476c-a0fb-f93350768716
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Claim Vanish proof dce3cf61647f: P2 M Ground Theory Heights  Heights Kleiman Claim Vanish proof dce3cf61647f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Claim Vanish proof dce3cf61647f construction uses the P2 M Ground Theory Heights  Heights Kleiman Claim Vanish proof dce3cf61647f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanish.lean#L94-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanish.lean#L94-L124

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanishCech
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ClaimVanish_proof_dce3cf61647f (h₁ : StepTwo.Statement.{u, w, w}) (h₂ : TwistVanish.Statement.{u, w})
    (h₃ : ClaimSeq.Statement.{u, w}) : ClaimVanish.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ClaimVanish».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_ClaimVanish_proof_dce3cf61647f
