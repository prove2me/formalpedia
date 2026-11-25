-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesEval_pow_1a9d7efbc52a
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesEval_pow_1a9d7efbc52a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:16:05.958393+00:00
-- url     : https://prove2.me/theorems/23250bab-c549-555b-b7ea-18acf7c2903d
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg int Series Eval pow 1a9d7efbc52a: P2 M Ground Theory Heights  Heights Chowla Selberg int Series Eval pow 1a9d7efbc52a
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg int Series Eval pow 1a9d7efbc52a construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg int Series Eval pow 1a9d7efbc52a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PDeltaIntSeries.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PDeltaIntSeries.lean#L64-L69

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

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesEval_pow_1a9d7efbc52a {F : PowerSeries ℤ} {z : ℂ} (hF : IntSeriesConv F ‖z‖) (m : ℕ) :
    intSeriesEval (F ^ m) z = intSeriesEval F z ^ m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«intSeriesEval_pow» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesEval_pow_1a9d7efbc52a
