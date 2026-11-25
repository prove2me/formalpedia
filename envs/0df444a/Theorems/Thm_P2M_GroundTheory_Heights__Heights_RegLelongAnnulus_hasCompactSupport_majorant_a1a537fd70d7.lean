-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_hasCompactSupport_majorant_a1a537fd70d7
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_hasCompactSupport_majorant_a1a537fd70d7
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:16:37.648916+00:00
-- url     : https://prove2.me/theorems/a4971677-3eaa-4768-b809-038cb142abcd
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus has Compact Support majorant a1a537fd70d7: P2 M Ground Theory Heights  Heights Reg Lelong Annulus has Compact Support majorant a1a537fd70d7
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus has Compact Support majorant a1a537fd70d7 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus has Compact Support majorant a1a537fd70d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L367-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L367-L376

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
variable {n : ℕ} (x : Fin n → ℂ)

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_hasCompactSupport_majorant_a1a537fd70d7 (s : ℝ) : HasCompactSupport (majorant x s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«hasCompactSupport_majorant» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_hasCompactSupport_majorant_a1a537fd70d7
