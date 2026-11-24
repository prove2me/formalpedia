-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_kernel_66dd3acd1271
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_kernel_66dd3acd1271
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:14.933538+00:00
-- url     : https://prove2.me/theorems/7a3b0dae-9e31-44f3-923d-dfefdc43fee7
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus continuous kernel 66dd3acd1271: P2 M Ground Theory Heights  Heights Reg Lelong Annulus continuous kernel 66dd3acd1271
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus continuous kernel 66dd3acd1271 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus continuous kernel 66dd3acd1271 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L129-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L129-L130

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_kernel_66dd3acd1271 (e : ℕ) : Continuous fun τ : ℝ => ((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«continuous_kernel» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_kernel_66dd3acd1271
