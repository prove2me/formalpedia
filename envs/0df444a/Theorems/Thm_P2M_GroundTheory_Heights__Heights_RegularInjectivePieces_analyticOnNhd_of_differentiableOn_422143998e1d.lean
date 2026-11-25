-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegularInjectivePieces_analyticOnNhd_of_differentiableOn_422143998e1d
-- name    : P2M_GroundTheory_Heights__Heights_RegularInjectivePieces_analyticOnNhd_of_differentiableOn_422143998e1d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:24.723057+00:00
-- url     : https://prove2.me/theorems/f3d86595-0f16-4991-ab97-5b7a7178a932
-- title:
--   P2 M Ground Theory Heights  Heights Regular Injective Pieces analytic On Nhd of differentiable On 422143998e1d: P2 M Ground Theory Heights  Heights Regular Injective Pieces analytic On Nhd of differen
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Injective Pieces analytic On Nhd of differentiable On 422143998e1d construction uses the P2 M Ground Theory Heights  Heights Regular Injective Pieces analytic On Nhd of differentiable On 422143998e1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularInjectivePieces.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularInjectivePieces.lean#L14-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularInjectivePieces
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularInjectivePieces
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
open MeasureTheory Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.RegularInjectivePieces

theorem P2M_GroundTheory_Heights__Heights_RegularInjectivePieces_analyticOnNhd_of_differentiableOn_422143998e1d {k m : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegularInjectivePieces».«analyticOnNhd_of_differentiableOn» := P2M_GroundTheory_Heights__Heights_RegularInjectivePieces_analyticOnNhd_of_differentiableOn_422143998e1d
