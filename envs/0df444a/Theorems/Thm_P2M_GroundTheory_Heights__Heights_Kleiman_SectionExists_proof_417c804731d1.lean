-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionExists_proof_417c804731d1
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionExists_proof_417c804731d1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:32:39.421797+00:00
-- url     : https://prove2.me/theorems/310154f1-fdc5-4842-9ae5-3e1b0b0ed3c8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Exists proof 417c804731d1: P2 M Ground Theory Heights  Heights Kleiman Section Exists proof 417c804731d1
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Exists proof 417c804731d1 construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Exists proof 417c804731d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionExists.lean#L103-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionExists.lean#L103-L125

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmplePowSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LeadingCoeffPosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionExists
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
open Filter
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionExists_proof_417c804731d1 (hcount : SectionCount.Statement.{u, w})
    (hpow : VeryAmplePow.Statement.{u, w}) (hlead : LeadingCoeffPos.Statement.{u, w}) :
    SectionExists.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionExists».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionExists_proof_417c804731d1
