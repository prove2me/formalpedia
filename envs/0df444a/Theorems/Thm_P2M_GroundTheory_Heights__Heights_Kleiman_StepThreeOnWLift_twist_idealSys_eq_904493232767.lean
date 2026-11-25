-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_twist_idealSys_eq_904493232767
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_twist_idealSys_eq_904493232767
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:58:56.994869+00:00
-- url     : https://prove2.me/theorems/8f24bb8c-b42c-5627-95bb-97565ae0e3fc
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Three On WLift twist ideal Sys eq 904493232767: P2 M Ground Theory Heights  Heights Kleiman Step Three On WLift twist ideal Sys eq 904493232767
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Three On WLift twist ideal Sys eq 904493232767 construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Three On WLift twist ideal Sys eq 904493232767 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWLift.lean#L138-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWLift.lean#L138-L142

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnWLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWLift
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
open GroundTheory.Heights₂.Heights.Kleiman.StepThreeOnWLift
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_twist_idealSys_eq_904493232767 (Q : SubSystem k x Ω) (P : Ideal (Poly k N)) :
    Q.twist (idealSys x P) = ((idealGraded x P).tildeSys 0).twist Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepThreeOnWLift».«twist_idealSys_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_twist_idealSys_eq_904493232767
