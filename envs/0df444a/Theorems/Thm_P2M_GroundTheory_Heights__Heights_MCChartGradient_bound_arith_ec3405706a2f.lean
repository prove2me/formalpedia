-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCChartGradient_bound_arith_ec3405706a2f
-- name    : P2M_GroundTheory_Heights__Heights_MCChartGradient_bound_arith_ec3405706a2f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:19.668331+00:00
-- url     : https://prove2.me/theorems/270065a6-8df8-4cae-8078-7625f1ab8aee
-- title:
--   P2 M Ground Theory Heights  Heights MCChart Gradient bound arith ec3405706a2f: P2 M Ground Theory Heights  Heights MCChart Gradient bound arith ec3405706a2f
-- statement:
--   The P2 M Ground Theory Heights  Heights MCChart Gradient bound arith ec3405706a2f construction uses the P2 M Ground Theory Heights  Heights MCChart Gradient bound arith ec3405706a2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartGradient.lean#L17-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartGradient.lean#L17-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartGradient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.MCChartGradient

theorem P2M_GroundTheory_Heights__Heights_MCChartGradient_bound_arith_ec3405706a2f (S A C₁ δ r e : ℝ) (k : ℕ) (hS : 0 ≤ S) (hA : 0 ≤ A) (hC₁ : 0 < C₁)
    (hδ : 0 < δ) (hr : 0 < r) (he : 1 ≤ e) :
    S * (1 + A * e) / ((C₁ * r)⁻¹ ^ k * δ) ≤ S * (1 + A) * C₁ ^ k / δ * r ^ k * e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCChartGradient».«bound_arith» := P2M_GroundTheory_Heights__Heights_MCChartGradient_bound_arith_ec3405706a2f
