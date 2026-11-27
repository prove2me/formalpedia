-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpInvariance_proof_ab77533650ef
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpInvariance_proof_ab77533650ef
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:32:28.617605+00:00
-- url     : https://prove2.me/theorems/6c33c348-ffc3-4592-a5e5-067ad9ad66bd
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Blow Up Invariance proof ab77533650ef: P2 M Ground Theory Heights  Heights Numbers DVR Blow Up Invariance proof ab77533650ef
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Blow Up Invariance proof ab77533650ef construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Blow Up Invariance proof ab77533650ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CycEvalCongrOnSupport.lean#L64-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CycEvalCongrOnSupport.lean#L64-L134

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BlowUpPushHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CycEvalCongrOnSupport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultAtPrimeAtMinimal_proof_af70a5a37a53

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpInvariance_proof_ab77533650ef (hvert : BlowUpVerticalPush.Statement.{u})
    (hdiv : BlowUpDivisorPush.Statement.{u}) (hhor : BlowUpHorizontalCorresp.Statement.{u})
    (hcomp : HorizontalComponentModel.Statement.{u}) (hfin : DivCycleFiniteSupport.Statement.{u}) :
    BlowUpInvariance.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BlowUpInvariance».«proof» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpInvariance_proof_ab77533650ef
