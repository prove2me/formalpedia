-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_hk_nonneg_301de9d1902f
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_hk_nonneg_301de9d1902f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:16:24.729879+00:00
-- url     : https://prove2.me/theorems/2dd74834-7714-4a39-bf50-13e6c70bd626
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus integral hk nonneg 301de9d1902f: P2 M Ground Theory Heights  Heights Reg Lelong Annulus integral hk nonneg 301de9d1902f
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus integral hk nonneg 301de9d1902f construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus integral hk nonneg 301de9d1902f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L275-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L275-L277

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_hk_nonneg_301de9d1902f (e k : ℕ) {v : ℝ} (h0 : 0 ≤ v) :
    0 ≤ ∫ w in (0 : ℝ)..v, hk k w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«integral_hk_nonneg» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_hk_nonneg_301de9d1902f
