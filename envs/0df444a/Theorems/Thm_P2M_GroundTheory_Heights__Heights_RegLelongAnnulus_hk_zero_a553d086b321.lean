-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_hk_zero_a553d086b321
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_hk_zero_a553d086b321
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:16:36.440475+00:00
-- url     : https://prove2.me/theorems/b781e633-2ea6-4358-bf6a-41e0fbf5ef2e
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus hk zero a553d086b321: P2 M Ground Theory Heights  Heights Reg Lelong Annulus hk zero a553d086b321
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus hk zero a553d086b321 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus hk zero a553d086b321 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L228-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L228-L231

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_hk_zero_a553d086b321 {k : ℕ} {v : ℝ} (hv : qk k ≤ v) : hk k v = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«hk_zero» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_hk_zero_a553d086b321
