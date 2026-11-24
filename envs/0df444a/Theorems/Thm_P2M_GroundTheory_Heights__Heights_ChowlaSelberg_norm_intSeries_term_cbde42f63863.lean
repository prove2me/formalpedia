-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_norm_intSeries_term_cbde42f63863
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_norm_intSeries_term_cbde42f63863
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:27.617272+00:00
-- url     : https://prove2.me/theorems/50fb82fe-9de4-4d2f-b411-0dc705bd5ff2
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg norm int Series term cbde42f63863: P2 M Ground Theory Heights  Heights Chowla Selberg norm int Series term cbde42f63863
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg norm int Series term cbde42f63863 construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg norm int Series term cbde42f63863 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PDeltaIntSeries.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PDeltaIntSeries.lean#L13-L15

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

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_norm_intSeries_term_cbde42f63863 (F : PowerSeries ℤ) (z : ℂ) (n : ℕ) :
    ‖((coeff n F : ℤ) : ℂ) * z ^ n‖ = |((coeff n F : ℤ) : ℝ)| * ‖z‖ ^ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«norm_intSeries_term» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_norm_intSeries_term_cbde42f63863
