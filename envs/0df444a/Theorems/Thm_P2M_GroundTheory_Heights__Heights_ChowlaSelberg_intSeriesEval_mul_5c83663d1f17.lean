-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesEval_mul_5c83663d1f17
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesEval_mul_5c83663d1f17
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:45.741654+00:00
-- url     : https://prove2.me/theorems/3aaccb19-83b3-5370-87e1-bef157150cdc
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg int Series Eval mul 5c83663d1f17: P2 M Ground Theory Heights  Heights Chowla Selberg int Series Eval mul 5c83663d1f17
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg int Series Eval mul 5c83663d1f17 construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg int Series Eval mul 5c83663d1f17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PDeltaIntSeries.lean#L34-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PDeltaIntSeries.lean#L34-L47

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

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesEval_mul_5c83663d1f17 {F G : PowerSeries ℤ} {z : ℂ} (hF : IntSeriesConv F ‖z‖)
    (hG : IntSeriesConv G ‖z‖) : intSeriesEval (F * G) z = intSeriesEval F z * intSeriesEval G z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«intSeriesEval_mul» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesEval_mul_5c83663d1f17
