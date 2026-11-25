-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_radialTransform_hk_le_c61936e6e318
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_radialTransform_hk_le_c61936e6e318
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:16:13.579803+00:00
-- url     : https://prove2.me/theorems/a4a69fb4-ff54-4213-a74d-5b5ac9216bd7
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus abs radial Transform hk le c61936e6e318: P2 M Ground Theory Heights  Heights Reg Lelong Annulus abs radial Transform hk le c61936e6e318
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus abs radial Transform hk le c61936e6e318 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus abs radial Transform hk le c61936e6e318 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L300-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L300-L312

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_radialTransform_hk_le_c61936e6e318 (e k : ℕ) {v : ℝ} (h0 : 0 ≤ v) :
    |radialTransform (e + 1) (hk k) v| ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«abs_radialTransform_hk_le» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_radialTransform_hk_le_c61936e6e318
