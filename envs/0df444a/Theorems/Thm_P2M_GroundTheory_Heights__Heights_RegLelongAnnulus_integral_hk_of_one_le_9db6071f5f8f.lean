-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_hk_of_one_le_9db6071f5f8f
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_hk_of_one_le_9db6071f5f8f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:17:17.168431+00:00
-- url     : https://prove2.me/theorems/d9809dbf-e037-5863-b8ac-95c0e2bfcf02
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus integral hk of one le 9db6071f5f8f: P2 M Ground Theory Heights  Heights Reg Lelong Annulus integral hk of one le 9db6071f5f8f
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus integral hk of one le 9db6071f5f8f construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus integral hk of one le 9db6071f5f8f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L242-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L242-L252

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_hk_of_one_le_9db6071f5f8f (e k : ℕ) {v : ℝ} (hv : 1 ≤ v) :
    ∫ w in (0 : ℝ)..v, hk k w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) = Ik e k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«integral_hk_of_one_le» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_hk_of_one_le_9db6071f5f8f
