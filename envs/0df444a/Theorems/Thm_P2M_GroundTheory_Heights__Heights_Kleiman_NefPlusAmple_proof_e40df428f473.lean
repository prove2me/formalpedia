-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_NefPlusAmple_proof_e40df428f473
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_NefPlusAmple_proof_e40df428f473
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:21:04.69502+00:00
-- url     : https://prove2.me/theorems/effb3965-3998-418f-aa6f-faccbe906785
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Nef Plus Ample proof e40df428f473: P2 M Ground Theory Heights  Heights Kleiman Nef Plus Ample proof e40df428f473
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Nef Plus Ample proof e40df428f473 construction uses the P2 M Ground Theory Heights  Heights Kleiman Nef Plus Ample proof e40df428f473 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L168-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L168-L198

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_NefPlusAmple_proof_e40df428f473 (hGA : GeneratedAmple.Statement.{u, w})
    (hK : VeryAmpleNefPlusAmple.Statement.{u, w}) (hJ : VeryAmpleTwistGenerated.Statement.{u, w}) :
    NefPlusAmple.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«NefPlusAmple».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_NefPlusAmple_proof_e40df428f473
