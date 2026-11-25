-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_hk_indicator_a5a1bc6852e4
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_hk_indicator_a5a1bc6852e4
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:32.212799+00:00
-- url     : https://prove2.me/theorems/35e415cc-de67-4131-8fe9-6ec2f980ec33
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto hk indicator a5a1bc6852e4: P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto hk indicator a5a1bc6852e4
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto hk indicator a5a1bc6852e4 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto hk indicator a5a1bc6852e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L422-L434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L422-L434

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_hk_indicator_a5a1bc6852e4 {ρ : ℝ} (hρ : 0 < ρ) (z : Fin n → ℂ) :
    Tendsto (fun k => hk k (euclPot (z - x) / ρ ^ 2)) atTop
      (𝓝 ((euclBall x ρ).indicator (fun _ => (1 : ℝ)) z)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«tendsto_hk_indicator» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_hk_indicator_a5a1bc6852e4
