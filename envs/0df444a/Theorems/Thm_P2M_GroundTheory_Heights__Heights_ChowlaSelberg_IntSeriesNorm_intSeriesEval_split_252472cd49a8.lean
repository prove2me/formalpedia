-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_intSeriesEval_split_252472cd49a8
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_intSeriesEval_split_252472cd49a8
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:24.523492+00:00
-- url     : https://prove2.me/theorems/43edaa05-2a8b-5a4c-844c-a4f2dd4d7c5e
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Norm int Series Eval split 252472cd49a8: P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Norm int Series Eval split 252472cd
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Norm int Series Eval split 252472cd49a8 construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Norm int Series Eval split 252472cd49a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PIntSeriesNorm.lean#L47-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PIntSeriesNorm.lean#L47-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PIntSeriesNorm
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
open PowerSeries
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesNorm

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_intSeriesEval_split_252472cd49a8 (hR : IntSeriesRing.Statement) {F : PowerSeries ℤ} {r : ℝ}
    (hr : 0 < r) (hF : IntSeriesConv F r) {p : ℕ} (hp : 0 < p) (s : ℂ) (hs : ‖s‖ ≤ r) :
    intSeriesEval F s = ∑ i : Fin p, s ^ (i : ℕ) * intSeriesEval (residuePart F p i) (s ^ p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«IntSeriesNorm».«intSeriesEval_split» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_intSeriesEval_split_252472cd49a8
