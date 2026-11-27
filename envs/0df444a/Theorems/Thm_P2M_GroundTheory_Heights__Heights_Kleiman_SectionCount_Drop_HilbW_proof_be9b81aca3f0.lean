-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_HilbW_proof_be9b81aca3f0
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_HilbW_proof_be9b81aca3f0
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:29:00.659139+00:00
-- url     : https://prove2.me/theorems/beb93540-4c9a-50bc-bc7b-0bd5e310398d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Hilb W proof be9b81aca3f0: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Hilb W proof be9b81aca3f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Hilb W proof be9b81aca3f0 construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Hilb W proof be9b81aca3f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropHilbW.lean#L35-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropHilbW.lean#L35-L143

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropHilbWSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleEmbedSectionsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleEmbedNumbersSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechH0SectionsHypothesesLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumPointSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropHilbW
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
open MvPolynomial Filter
noncomputable section
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_HilbW_proof_be9b81aca3f0
    (hPt : PrimeFiltration.Point.Statement.{u, w})
    (hRes : Restriction.Statement.{u, w})
    (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w})
    (hLT : LineTwist.Statement.{u, w})
    (hRT : RestrictTwist.Statement.{u, w})
    (hIR : InterNumRestrict.Statement.{u, w})
    (hES : VeryAmpleEmbed.Sections.Statement.{u, w})
    (hEN : VeryAmpleEmbed.Numbers.Statement.{u, w})
    (hH0 : CechZerothCohomologySections.Statement.{u, w, w})
    (hHP : HilbertPositive.Statement.{u, w})
    (hHPt : HilbertPoint.Statement.{u, w})
    (hTie : InterNumTie.Statement.{u, w})
    (hIP : InterNumPoint.Statement.{u, w}) :
    SectionCount.Drop.HilbW.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«HilbW».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_HilbW_proof_be9b81aca3f0
