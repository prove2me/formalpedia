-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_eval_mul_b7faa16843e5
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_eval_mul_b7faa16843e5
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:42.67291+00:00
-- url     : https://prove2.me/theorems/9aeb962c-1274-5a49-9698-f1f5eeaf1c4e
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring eval mul b7faa16843e5: P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring eval mul b7faa16843e5
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring eval mul b7faa16843e5 construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring eval mul b7faa16843e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PIntSeriesRing.lean#L74-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PIntSeriesRing.lean#L74-L86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PIntSeriesRing
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
open PowerSeries Finset
noncomputable section
open GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesRing

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_eval_mul_b7faa16843e5 {F G : PowerSeries ℤ} {r : ℝ} (hF : IntSeriesConv F r) (hG : IntSeriesConv G r)
    {z : ℂ} (hz : ‖z‖ ≤ r) : intSeriesEval (F * G) z = intSeriesEval F z * intSeriesEval G z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«IntSeriesRing».«eval_mul» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_eval_mul_b7faa16843e5
