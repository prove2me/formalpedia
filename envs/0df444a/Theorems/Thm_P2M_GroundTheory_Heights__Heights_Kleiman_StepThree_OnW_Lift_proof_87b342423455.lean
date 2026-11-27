-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Lift_proof_87b342423455
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Lift_proof_87b342423455
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:29:37.393788+00:00
-- url     : https://prove2.me/theorems/1e14bf12-38d6-5825-9c68-5acb37442a65
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Three On W Lift proof 87b342423455: P2 M Ground Theory Heights  Heights Kleiman Step Three On W Lift proof 87b342423455
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Three On W Lift proof 87b342423455 construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Three On W Lift proof 87b342423455 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWLift.lean#L277-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWLift.lean#L277-L293

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnWLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWLift
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ClaimVanish_proof_dce3cf61647f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_proof_00af9cf61dad

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
open StepThreeOnWLift

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Lift_proof_87b342423455 (hSeq : ClaimSeq.Statement.{u, w}) (hVan : ClaimVanish.Statement.{u, w})
    (hTwo : StepTwo.Statement.{u, w, w}) : StepThree.OnW.Lift.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepThree».«OnW».«Lift».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Lift_proof_87b342423455
