-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_contDiff_logDistSmooth_44f279e79d7f
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_contDiff_logDistSmooth_44f279e79d7f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:16:43.665521+00:00
-- url     : https://prove2.me/theorems/6f3eb63b-010d-49ca-b545-d1c0ab98ead9
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus cont Diff log Dist Smooth 44f279e79d7f: P2 M Ground Theory Heights  Heights Reg Lelong Annulus cont Diff log Dist Smooth 44f279e79d7f
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus cont Diff log Dist Smooth 44f279e79d7f construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus cont Diff log Dist Smooth 44f279e79d7f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L407-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L407-L409

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_contDiff_logDistSmooth_44f279e79d7f {r : ℝ} (hr : 0 < r) : ContDiff ℝ ∞ (logDistSmooth x hr) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«contDiff_logDistSmooth» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_contDiff_logDistSmooth_44f279e79d7f
