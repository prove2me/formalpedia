-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_diff_of_le_d2a53db5a632
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_diff_of_le_d2a53db5a632
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:37.953932+00:00
-- url     : https://prove2.me/theorems/3e4ef748-26d4-4ac7-8685-3f32cd0be29f
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform diff of le d2a53db5a632: P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform diff of le d2a53db5a632
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform diff of le d2a53db5a632 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform diff of le d2a53db5a632 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L486-L494
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L486-L494

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
variable {r s : ℝ} (e : ℕ)

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_diff_of_le_d2a53db5a632 (hr : 0 < r) (hrs : r ≤ s) (k : ℕ) {t : ℝ} (h0 : 0 ≤ t)
    (ht : t ≤ pk k * r ^ 2) :
    radialTransform (e + 1) (hk k) (t / s ^ 2) - radialTransform (e + 1) (hk k) (t / r ^ 2) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«radialTransform_diff_of_le» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_diff_of_le_d2a53db5a632
