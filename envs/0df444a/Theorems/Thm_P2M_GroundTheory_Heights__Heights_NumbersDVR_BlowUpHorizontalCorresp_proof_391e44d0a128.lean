-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpHorizontalCorresp_proof_391e44d0a128
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpHorizontalCorresp_proof_391e44d0a128
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:34:12.291099+00:00
-- url     : https://prove2.me/theorems/ff73de40-e686-5772-b14e-0a417896c2f4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Blow Up Horizontal Corresp proof 391e44d0a128: P2 M Ground Theory Heights  Heights Numbers DVR Blow Up Horizontal Corresp proof 391e44d0a128
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Blow Up Horizontal Corresp proof 391e44d0a128 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Blow Up Horizontal Corresp proof 391e44d0a128 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpHorizontalCorresp.lean#L15-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpHorizontalCorresp.lean#L15-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalCorresp
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpHorizontalCorresp_proof_391e44d0a128 (hsat : BlowUpHorizontalSat.Statement.{u})
    (hmult : BlowUpHorizontalMult.Statement.{u}) (hlift : BlowUpHorizontalLift.Statement.{u})
    (hstrict : BlowUpHorizontalStrict.Statement.{u}) : BlowUpHorizontalCorresp.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BlowUpHorizontalCorresp».«proof» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpHorizontalCorresp_proof_391e44d0a128
