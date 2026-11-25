-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_abs_coeff_pentagonalSeries_le_742b2301d919
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_abs_coeff_pentagonalSeries_le_742b2301d919
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:33.52626+00:00
-- url     : https://prove2.me/theorems/24878b9d-029c-595c-aa88-6e3217f78b65
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg abs coeff pentagonal Series le 742b2301d919: P2 M Ground Theory Heights  Heights Chowla Selberg abs coeff pentagonal Series le 742b2301d919
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg abs coeff pentagonal Series le 742b2301d919 construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg abs coeff pentagonal Series le 742b2301d919 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PDeltaIntSeries.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PDeltaIntSeries.lean#L71-L77

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

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_abs_coeff_pentagonalSeries_le_742b2301d919 (n : ℕ) :
    |((coeff n (pentagonalSeries ℤ) : ℤ) : ℝ)| ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«abs_coeff_pentagonalSeries_le» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_abs_coeff_pentagonalSeries_le_742b2301d919
