-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_comp_div_sq_378fa9759947
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_comp_div_sq_378fa9759947
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:17:31.469154+00:00
-- url     : https://prove2.me/theorems/98e65b15-c1fd-4461-b3bd-e44458b99b32
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus integral comp div sq 378fa9759947: P2 M Ground Theory Heights  Heights Reg Lelong Annulus integral comp div sq 378fa9759947
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus integral comp div sq 378fa9759947 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus integral comp div sq 378fa9759947 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L135-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L135-L150

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_comp_div_sq_378fa9759947 (e : ℕ) (h : ℝ → ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) (t : ℝ) :
    ∫ τ in (0 : ℝ)..t, h (τ / ρ ^ 2) * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) =
      ρ ^ (2 * (e + 1)) * ∫ w in (0 : ℝ)..t / ρ ^ 2, h w * (((e + 1 : ℕ) : ℝ) * w ^ (e + 1 - 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«integral_comp_div_sq» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integral_comp_div_sq_378fa9759947
