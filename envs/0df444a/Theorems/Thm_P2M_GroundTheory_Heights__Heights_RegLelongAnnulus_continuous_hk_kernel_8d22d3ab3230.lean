-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_hk_kernel_8d22d3ab3230
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_hk_kernel_8d22d3ab3230
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:27.578907+00:00
-- url     : https://prove2.me/theorems/ad3861d0-77f4-441b-b1b4-8f377bb25250
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus continuous hk kernel 8d22d3ab3230: P2 M Ground Theory Heights  Heights Reg Lelong Annulus continuous hk kernel 8d22d3ab3230
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus continuous hk kernel 8d22d3ab3230 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus continuous hk kernel 8d22d3ab3230 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L238-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L238-L240

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.RegLelongAnnulus

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_hk_kernel_8d22d3ab3230 (e k : ℕ) :
    Continuous fun w : ℝ => hk k w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«continuous_hk_kernel» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_hk_kernel_8d22d3ab3230
