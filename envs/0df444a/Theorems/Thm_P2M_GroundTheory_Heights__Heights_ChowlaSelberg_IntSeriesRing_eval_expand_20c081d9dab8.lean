-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_eval_expand_20c081d9dab8
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_eval_expand_20c081d9dab8
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:42.379096+00:00
-- url     : https://prove2.me/theorems/33e6860d-41f1-463a-a481-29af43b55d90
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring eval expand 20c081d9dab8: P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring eval expand 20c081d9dab8
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring eval expand 20c081d9dab8 construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring eval expand 20c081d9dab8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PIntSeriesRing.lean#L100-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PIntSeriesRing.lean#L100-L108

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

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_eval_expand_20c081d9dab8 {p : ℕ} (hp : p ≠ 0) (F : PowerSeries ℤ) (z : ℂ) :
    intSeriesEval (expand p hp F) z = intSeriesEval F (z ^ p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«IntSeriesRing».«eval_expand» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_eval_expand_20c081d9dab8
