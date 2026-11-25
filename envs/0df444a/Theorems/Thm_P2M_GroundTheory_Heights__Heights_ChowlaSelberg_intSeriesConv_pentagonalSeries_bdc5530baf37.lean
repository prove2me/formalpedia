-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_pentagonalSeries_bdc5530baf37
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_pentagonalSeries_bdc5530baf37
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:25.31057+00:00
-- url     : https://prove2.me/theorems/cbfb4f37-6beb-4924-a693-bcf3bce740a3
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg int Series Conv pentagonal Series bdc5530baf37: P2 M Ground Theory Heights  Heights Chowla Selberg int Series Conv pentagonal Series bdc5530baf37
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg int Series Conv pentagonal Series bdc5530baf37 construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg int Series Conv pentagonal Series bdc5530baf37 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PDeltaIntSeries.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PDeltaIntSeries.lean#L79-L82

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

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_pentagonalSeries_bdc5530baf37 {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    IntSeriesConv (pentagonalSeries ℤ) r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«intSeriesConv_pentagonalSeries» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_pentagonalSeries_bdc5530baf37
