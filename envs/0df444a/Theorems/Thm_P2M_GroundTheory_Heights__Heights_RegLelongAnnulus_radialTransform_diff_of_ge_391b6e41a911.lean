-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_diff_of_ge_391b6e41a911
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_diff_of_ge_391b6e41a911
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:32.501793+00:00
-- url     : https://prove2.me/theorems/c38f8cc4-191e-415f-b546-8ed9b491a273
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform diff of ge 391b6e41a911: P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform diff of ge 391b6e41a911
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform diff of ge 391b6e41a911 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform diff of ge 391b6e41a911 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L496-L501
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L496-L501

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_diff_of_ge_391b6e41a911 (hr : 0 < r) (hrs : r ≤ s) (k : ℕ) {t : ℝ} (ht : s ^ 2 ≤ t) :
    radialTransform (e + 1) (hk k) (t / s ^ 2) - radialTransform (e + 1) (hk k) (t / r ^ 2) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«radialTransform_diff_of_ge» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_diff_of_ge_391b6e41a911
