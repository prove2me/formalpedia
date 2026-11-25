-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_norm_prod_one_sub_pow_le_6387f8597f85
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_norm_prod_one_sub_pow_le_6387f8597f85
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:16:24.714823+00:00
-- url     : https://prove2.me/theorems/a14f24ad-d15c-4f2a-adc6-1c921fe5c7d9
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg norm prod one sub pow le 6387f8597f85: P2 M Ground Theory Heights  Heights Chowla Selberg norm prod one sub pow le 6387f8597f85
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg norm prod one sub pow le 6387f8597f85 construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg norm prod one sub pow le 6387f8597f85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PDeltaIntSeries.lean#L84-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PDeltaIntSeries.lean#L84-L100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_DeltaIntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PDeltaIntSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ChowlaSelberg
open PowerSeries Filter Topology Finset
open scoped Real
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_norm_prod_one_sub_pow_le_6387f8597f85 {x : ℂ} (hx : ‖x‖ < 1) (k n : ℕ) :
    ‖∏ i ∈ range (n + 1), (1 - x ^ (k + i + 1))‖ ≤ Real.exp (1 - ‖x‖)⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«norm_prod_one_sub_pow_le» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_norm_prod_one_sub_pow_le_6387f8597f85
