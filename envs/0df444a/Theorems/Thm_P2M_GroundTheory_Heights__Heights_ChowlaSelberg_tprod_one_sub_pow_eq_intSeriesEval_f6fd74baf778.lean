-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_tprod_one_sub_pow_eq_intSeriesEval_f6fd74baf778
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_tprod_one_sub_pow_eq_intSeriesEval_f6fd74baf778
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:16:54.821096+00:00
-- url     : https://prove2.me/theorems/1f194509-caa4-4e6f-9754-ea3c017159cb
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg tprod one sub pow eq int Series Eval f6fd74baf778: P2 M Ground Theory Heights  Heights Chowla Selberg tprod one sub pow eq int Series Eval f6fd74baf7
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg tprod one sub pow eq int Series Eval f6fd74baf778 construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg tprod one sub pow eq int Series Eval f6fd74baf778 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PDeltaIntSeries.lean#L102-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PDeltaIntSeries.lean#L102-L148

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

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_tprod_one_sub_pow_eq_intSeriesEval_f6fd74baf778 {x : ℂ} (hx : ‖x‖ < 1) :
    ∏' n, (1 - x ^ (n + 1)) = intSeriesEval (pentagonalSeries ℤ) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«tprod_one_sub_pow_eq_intSeriesEval» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_tprod_one_sub_pow_eq_intSeriesEval_f6fd74baf778
