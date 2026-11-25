-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_mul_8992812ba236
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_mul_8992812ba236
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:59.722368+00:00
-- url     : https://prove2.me/theorems/b6bd50ed-1a0b-5a30-8d5f-f7a271cc6cc3
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg int Series Conv mul 8992812ba236: P2 M Ground Theory Heights  Heights Chowla Selberg int Series Conv mul 8992812ba236
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg int Series Conv mul 8992812ba236 construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg int Series Conv mul 8992812ba236 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PDeltaIntSeries.lean#L17-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PDeltaIntSeries.lean#L17-L32

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

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_mul_8992812ba236 {F G : PowerSeries ℤ} {r : ℝ} (hr : 0 ≤ r) (hF : IntSeriesConv F r)
    (hG : IntSeriesConv G r) : IntSeriesConv (F * G) r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«intSeriesConv_mul» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_mul_8992812ba236
