-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_proof_00af9cf61dad
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_proof_00af9cf61dad
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:21:32.1068+00:00
-- url     : https://prove2.me/theorems/083b5bbb-5887-4ca0-b032-72994dd6d1bc
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Surjective Closed proof 00af9cf61dad: P2 M Ground Theory Heights  Heights Kleiman Surjective Closed proof 00af9cf61dad
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Surjective Closed proof 00af9cf61dad construction uses the P2 M Ground Theory Heights  Heights Kleiman Surjective Closed proof 00af9cf61dad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSurjectiveClosed.lean#L197-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSurjectiveClosed.lean#L197-L299

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
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
open GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_proof_00af9cf61dad (hExt : Extension.Statement.{u, w, w})
    (hFam : IdealTwistFamily.Statement.{u, w}) (hVan : TildeVanish.Statement.{u, w, w}) :
    SurjectiveClosed.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SurjectiveClosed».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_proof_00af9cf61dad
