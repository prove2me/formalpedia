-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_conv_mono_03f353ad5712
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_conv_mono_03f353ad5712
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:35.682065+00:00
-- url     : https://prove2.me/theorems/588102ff-4812-552a-a952-fbe4fda2f5ce
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring conv mono 03f353ad5712: P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring conv mono 03f353ad5712
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring conv mono 03f353ad5712 construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring conv mono 03f353ad5712 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PIntSeriesRing.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PIntSeriesRing.lean#L14-L17

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

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_conv_mono_03f353ad5712 {F : PowerSeries ℤ} {r r' : ℝ} (hF : IntSeriesConv F r) (h0 : 0 ≤ r')
    (hle : r' ≤ r) : IntSeriesConv F r' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«IntSeriesRing».«conv_mono» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_conv_mono_03f353ad5712
