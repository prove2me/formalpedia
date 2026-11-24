-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_kernel_nonneg_9afb1b251b85
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_kernel_nonneg_9afb1b251b85
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:27.212503+00:00
-- url     : https://prove2.me/theorems/64bc28ea-2a9b-4346-95eb-a20b52ba8928
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus kernel nonneg 9afb1b251b85: P2 M Ground Theory Heights  Heights Reg Lelong Annulus kernel nonneg 9afb1b251b85
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus kernel nonneg 9afb1b251b85 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus kernel nonneg 9afb1b251b85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L132-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L132-L133

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_kernel_nonneg_9afb1b251b85 (e : ℕ) {w : ℝ} (hw : 0 ≤ w) : 0 ≤ ((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«kernel_nonneg» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_kernel_nonneg_9afb1b251b85
