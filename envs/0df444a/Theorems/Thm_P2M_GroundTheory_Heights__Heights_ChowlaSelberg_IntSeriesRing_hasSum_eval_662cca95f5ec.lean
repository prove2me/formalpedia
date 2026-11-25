-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_hasSum_eval_662cca95f5ec
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_hasSum_eval_662cca95f5ec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:30.109105+00:00
-- url     : https://prove2.me/theorems/97ec1077-c5fa-4b3c-bbb1-8294d8e7b346
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring has Sum eval 662cca95f5ec: P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring has Sum eval 662cca95f5ec
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring has Sum eval 662cca95f5ec construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring has Sum eval 662cca95f5ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PIntSeriesRing.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PIntSeriesRing.lean#L70-L72

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

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_hasSum_eval_662cca95f5ec {F : PowerSeries ℤ} {r : ℝ} (hF : IntSeriesConv F r) {z : ℂ}
    (hz : ‖z‖ ≤ r) : HasSum (fun n ↦ ((coeff n F : ℤ) : ℂ) * z ^ n) (intSeriesEval F z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«IntSeriesRing».«hasSum_eval» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_hasSum_eval_662cca95f5ec
