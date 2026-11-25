-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_mul_newVar_sub_mem_8482d2e8e889
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_mul_newVar_sub_mem_8482d2e8e889
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:11:53.65426+00:00
-- url     : https://prove2.me/theorems/b0333887-d78b-4d85-bcc3-e1d6054dedce
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR lift Form mul new Var sub mem 8482d2e8e889: P2 M Ground Theory Heights  Heights Numbers DVR lift Form mul new Var sub mem 8482d2e8e889
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR lift Form mul new Var sub mem 8482d2e8e889 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR lift Form mul new Var sub mem 8482d2e8e889 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpLocalChart.lean#L99-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpLocalChart.lean#L99-L103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpLocalChart
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
noncomputable section
variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_mul_newVar_sub_mem_8482d2e8e889 (P : Ideal (MRing ι R)) (u : J → MRing ι R) (j k : J) :
    liftForm (u j) * newVar k - liftForm (u k) * newVar j ∈ blowUpOf P u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«liftForm_mul_newVar_sub_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_mul_newVar_sub_mem_8482d2e8e889
