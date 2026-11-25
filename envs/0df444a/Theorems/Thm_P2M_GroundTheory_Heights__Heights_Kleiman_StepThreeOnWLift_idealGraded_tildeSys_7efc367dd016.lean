-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_idealGraded_tildeSys_7efc367dd016
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_idealGraded_tildeSys_7efc367dd016
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:59:54.789336+00:00
-- url     : https://prove2.me/theorems/0f90fc45-b748-496b-bc19-629a51ef2360
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Three On WLift ideal Graded tilde Sys 7efc367dd016: P2 M Ground Theory Heights  Heights Kleiman Step Three On WLift ideal Graded tilde Sys 7efc367dd016
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Three On WLift ideal Graded tilde Sys 7efc367dd016 construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Three On WLift ideal Graded tilde Sys 7efc367dd016 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWLift.lean#L117-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWLift.lean#L117-L136

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_idealGraded_tildeSys_7efc367dd016 (P : Ideal (Poly k N)) : (idealGraded x P).tildeSys 0 = idealSys x P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepThreeOnWLift».«idealGraded_tildeSys» := P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_idealGraded_tildeSys_7efc367dd016
