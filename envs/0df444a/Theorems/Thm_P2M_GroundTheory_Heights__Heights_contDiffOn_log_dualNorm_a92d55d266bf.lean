-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiffOn_log_dualNorm_a92d55d266bf
-- name    : P2M_GroundTheory_Heights__Heights_contDiffOn_log_dualNorm_a92d55d266bf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:29.259488+00:00
-- url     : https://prove2.me/theorems/63a54d41-cdbe-4e3a-9f04-2db40f42322b
-- title:
--   P2 M Ground Theory Heights  Heights cont Diff On log dual Norm a92d55d266bf: P2 M Ground Theory Heights  Heights cont Diff On log dual Norm a92d55d266bf
-- statement:
--   The P2 M Ground Theory Heights  Heights cont Diff On log dual Norm a92d55d266bf construction uses the P2 M Ground Theory Heights  Heights cont Diff On log dual Norm a92d55d266bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceSectionMass.lean#L13-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceSectionMass.lean#L13-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceExhaustion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
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
open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem P2M_GroundTheory_Heights__Heights_contDiffOn_log_dualNorm_a92d55d266bf {n : ℕ} (h : HermNorm n) :
    ContDiffOn ℝ ∞ (fun x : Fin n → ℂ => Real.log (h.dualNorm x)) {0}ᶜ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«contDiffOn_log_dualNorm» := P2M_GroundTheory_Heights__Heights_contDiffOn_log_dualNorm_a92d55d266bf
