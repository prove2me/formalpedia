-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_contDiff_annWeight_e989979f7f15
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_contDiff_annWeight_e989979f7f15
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:16:43.350743+00:00
-- url     : https://prove2.me/theorems/d47d132e-33eb-4806-8661-046c6e9ed917
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus cont Diff ann Weight e989979f7f15: P2 M Ground Theory Heights  Heights Reg Lelong Annulus cont Diff ann Weight e989979f7f15
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus cont Diff ann Weight e989979f7f15 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus cont Diff ann Weight e989979f7f15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L445-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L445-L447

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_contDiff_annWeight_e989979f7f15 (k : ℕ) : ContDiff ℝ ∞ (annWeight r s e k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«contDiff_annWeight» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_contDiff_annWeight_e989979f7f15
