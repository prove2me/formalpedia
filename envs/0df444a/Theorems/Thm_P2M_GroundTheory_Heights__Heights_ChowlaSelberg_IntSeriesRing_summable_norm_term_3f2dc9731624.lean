-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_summable_norm_term_3f2dc9731624
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_summable_norm_term_3f2dc9731624
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:33.249805+00:00
-- url     : https://prove2.me/theorems/d9917317-b729-4d0c-af95-d3caa0757535
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring summable norm term 3f2dc9731624: P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring summable norm term 3f2dc9731624
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring summable norm term 3f2dc9731624 construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Ring summable norm term 3f2dc9731624 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PIntSeriesRing.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PIntSeriesRing.lean#L64-L68

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

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_summable_norm_term_3f2dc9731624 {F : PowerSeries ℤ} {r : ℝ} (hF : IntSeriesConv F r) {z : ℂ}
    (hz : ‖z‖ ≤ r) : Summable fun n ↦ ‖((coeff n F : ℤ) : ℂ) * z ^ n‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«IntSeriesRing».«summable_norm_term» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_summable_norm_term_3f2dc9731624
