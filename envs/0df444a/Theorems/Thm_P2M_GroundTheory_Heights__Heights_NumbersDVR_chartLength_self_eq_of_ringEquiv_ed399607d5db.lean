-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_chartLength_self_eq_of_ringEquiv_ed399607d5db
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_chartLength_self_eq_of_ringEquiv_ed399607d5db
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:10:59.364424+00:00
-- url     : https://prove2.me/theorems/3bf28dcb-c762-4279-b45c-9db0e7a6b3f7
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR chart Length self eq of ring Equiv ed399607d5db: P2 M Ground Theory Heights  Heights Numbers DVR chart Length self eq of ring Equiv ed399607d5db
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR chart Length self eq of ring Equiv ed399607d5db construction uses the P2 M Ground Theory Heights  Heights Numbers DVR chart Length self eq of ring Equiv ed399607d5db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpHorizontalChartLength.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpHorizontalChartLength.lean#L31-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontalMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalChartLength
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_chartLength_self_eq_of_ringEquiv_ed399607d5db {Q Q' : Type*} [CommRing Q] [CommRing Q'] (τ : Q ≃+* Q') :
    Module.length Q Q = Module.length Q' Q' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«chartLength_self_eq_of_ringEquiv» := P2M_GroundTheory_Heights__Heights_NumbersDVR_chartLength_self_eq_of_ringEquiv_ed399607d5db
