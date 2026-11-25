-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_isOpen_ratPreimage_0d182ed088fb
-- name    : P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_isOpen_ratPreimage_0d182ed088fb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:57.052708+00:00
-- url     : https://prove2.me/theorems/597f80ba-97b4-40df-8739-44afcab7697d
-- title:
--   P2 M Ground Theory Heights  Heights Rat Sheet No Chart Null is Open rat Preimage 0d182ed088fb: P2 M Ground Theory Heights  Heights Rat Sheet No Chart Null is Open rat Preimage 0d182ed088fb
-- statement:
--   The P2 M Ground Theory Heights  Heights Rat Sheet No Chart Null is Open rat Preimage 0d182ed088fb construction uses the P2 M Ground Theory Heights  Heights Rat Sheet No Chart Null is Open rat Preimage 0d182ed088fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatSheetNoChartNull.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatSheetNoChartNull.lean#L24-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetNoChartNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatSheetNoChartNull
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
noncomputable section
open GroundTheory.Heights₂.Heights.RatSheetNoChartNull
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_isOpen_ratPreimage_0d182ed088fb (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    {S : Set (Fin d → ℂ)} (hS : IsOpen S) :
    IsOpen ({x | eval x q ≠ 0} ∩ RatChart.ratMap p q ⁻¹' S) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RatSheetNoChartNull».«isOpen_ratPreimage» := P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_isOpen_ratPreimage_0d182ed088fb
