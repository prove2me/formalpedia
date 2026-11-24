-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_pow_36e45add25b5
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_pow_36e45add25b5
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:54.668861+00:00
-- url     : https://prove2.me/theorems/12373131-9688-4688-bc5c-47e3112d50ff
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg int Series Conv pow 36e45add25b5: P2 M Ground Theory Heights  Heights Chowla Selberg int Series Conv pow 36e45add25b5
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg int Series Conv pow 36e45add25b5 construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg int Series Conv pow 36e45add25b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PDeltaIntSeries.lean#L58-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PDeltaIntSeries.lean#L58-L62

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

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_pow_36e45add25b5 {F : PowerSeries ℤ} {r : ℝ} (hr : 0 ≤ r) (hF : IntSeriesConv F r)
    (m : ℕ) : IntSeriesConv (F ^ m) r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«intSeriesConv_pow» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_pow_36e45add25b5
