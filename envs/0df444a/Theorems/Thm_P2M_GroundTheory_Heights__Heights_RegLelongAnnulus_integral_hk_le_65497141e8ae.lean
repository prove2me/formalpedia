-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_hk_le_65497141e8ae
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_hk_le_65497141e8ae
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:26.549793+00:00
-- url     : https://prove2.me/theorems/b72a78f3-7437-44df-8aee-caa3177ceb59
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus integral hk le 65497141e8ae: P2 M Ground Theory Heights  Heights Reg Lelong Annulus integral hk le 65497141e8ae
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus integral hk le 65497141e8ae construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus integral hk le 65497141e8ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L268-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L268-L273

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_hk_le_65497141e8ae (e k : ℕ) {v : ℝ} (h0 : 0 ≤ v) :
    ∫ w in (0 : ℝ)..v, hk k w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) ≤ v ^ (e + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«integral_hk_le» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_hk_le_65497141e8ae
