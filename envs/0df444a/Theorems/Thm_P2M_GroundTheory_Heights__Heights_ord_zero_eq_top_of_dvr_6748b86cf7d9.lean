-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ord_zero_eq_top_of_dvr_6748b86cf7d9
-- name    : P2M_GroundTheory_Heights__Heights_ord_zero_eq_top_of_dvr_6748b86cf7d9
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:32.343874+00:00
-- url     : https://prove2.me/theorems/a8974970-45ca-41dd-8df7-a38cfd40067d
-- title:
--   P2 M Ground Theory Heights  Heights ord zero eq top of dvr 6748b86cf7d9: P2 M Ground Theory Heights  Heights ord zero eq top of dvr 6748b86cf7d9
-- statement:
--   The P2 M Ground Theory Heights  Heights ord zero eq top of dvr 6748b86cf7d9 construction uses the P2 M Ground Theory Heights  Heights ord zero eq top of dvr 6748b86cf7d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PointLocalRingOrder.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PointLocalRingOrder.lean#L67-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PointLocalRingOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Topology
noncomputable section
variable {σ : Type*}

theorem P2M_GroundTheory_Heights__Heights_ord_zero_eq_top_of_dvr_6748b86cf7d9 (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    Ring.ord R 0 = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ord_zero_eq_top_of_dvr» := P2M_GroundTheory_Heights__Heights_ord_zero_eq_top_of_dvr_6748b86cf7d9
