-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodPointBranch_analyticOnNhd_of_differentiableOn_bf6eac09d233
-- name    : P2M_GroundTheory_Heights__Heights_GoodPointBranch_analyticOnNhd_of_differentiableOn_bf6eac09d233
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:20:52.521794+00:00
-- url     : https://prove2.me/theorems/0b249805-64cb-4489-b8ee-34730f8df1a8
-- title:
--   P2 M Ground Theory Heights  Heights Good Point Branch analytic On Nhd of differentiable On bf6eac09d233: P2 M Ground Theory Heights  Heights Good Point Branch analytic On Nhd of differentiable On bf6e
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Point Branch analytic On Nhd of differentiable On bf6eac09d233 construction uses the P2 M Ground Theory Heights  Heights Good Point Branch analytic On Nhd of differentiable On bf6eac09d233 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointBranchSlice.lean#L63-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointBranchSlice.lean#L63-L72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelFibreNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GoodPointBranchSlice
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
open MvPolynomial Filter Topology Matrix ComplexSets Metric Set
noncomputable section
open GroundTheory.Heights₂.Heights.GoodPointBranch

theorem P2M_GroundTheory_Heights__Heights_GoodPointBranch_analyticOnNhd_of_differentiableOn_bf6eac09d233 {k m : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodPointBranch».«analyticOnNhd_of_differentiableOn» := P2M_GroundTheory_Heights__Heights_GoodPointBranch_analyticOnNhd_of_differentiableOn_bf6eac09d233
