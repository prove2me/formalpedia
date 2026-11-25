-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_radialTransform_diff_5c78029be736
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_radialTransform_diff_5c78029be736
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:18:01.934851+00:00
-- url     : https://prove2.me/theorems/7b2feb7b-346f-48fc-83c5-cc4b99b36677
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto radial Transform diff 5c78029be736: P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto radial Transform diff 5c78029be736
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto radial Transform diff 5c78029be736 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto radial Transform diff 5c78029be736 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L505-L528
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L505-L528

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
variable {n : ℕ} (x : Fin n → ℂ)

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_radialTransform_diff_5c78029be736 (hr : 0 < r) (hrs : r ≤ s) (z : Fin n → ℂ) :
    Tendsto (fun k => radialTransform (e + 1) (hk k) (euclPot (z - x) / s ^ 2) -
        radialTransform (e + 1) (hk k) (euclPot (z - x) / r ^ 2)) atTop
      (𝓝 ((euclBall x s \ euclBall x r).indicator (fun _ => (1 : ℝ)) z)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«tendsto_radialTransform_diff» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_radialTransform_diff_5c78029be736
