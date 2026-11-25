-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_conv_expand_81eea0c6186f
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_conv_expand_81eea0c6186f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:54.96427+00:00
-- url     : https://prove2.me/theorems/46cc74df-06d9-41a5-935e-06c06aef1cc1
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring conv expand 81eea0c6186f: P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring conv expand 81eea0c6186f
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring conv expand 81eea0c6186f construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring conv expand 81eea0c6186f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PIntSeriesRing.lean#L91-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PIntSeriesRing.lean#L91-L98

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

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_conv_expand_81eea0c6186f {p : ℕ} (hp : p ≠ 0) {F : PowerSeries ℤ} {r : ℝ}
    (hF : IntSeriesConv F (r ^ p)) : IntSeriesConv (expand p hp F) r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«IntSeriesRing».«conv_expand» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_conv_expand_81eea0c6186f
