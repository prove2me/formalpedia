-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_hk_of_le_64a107755ae3
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_hk_of_le_64a107755ae3
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:55.104831+00:00
-- url     : https://prove2.me/theorems/e8453aaf-a7f1-4672-ada8-5fcb5e41182a
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform hk of le 64a107755ae3: P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform hk of le 64a107755ae3
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform hk of le 64a107755ae3 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform hk of le 64a107755ae3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L254-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L254-L257

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_hk_of_le_64a107755ae3 (e k : ℕ) {v : ℝ} (h0 : 0 ≤ v) (hv : v ≤ pk k) :
    radialTransform (e + 1) (hk k) v = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«radialTransform_hk_of_le» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_hk_of_le_64a107755ae3
