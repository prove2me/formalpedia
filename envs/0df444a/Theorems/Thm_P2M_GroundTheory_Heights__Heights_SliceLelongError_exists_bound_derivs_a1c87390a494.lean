-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceLelongError_exists_bound_derivs_a1c87390a494
-- name    : P2M_GroundTheory_Heights__Heights_SliceLelongError_exists_bound_derivs_a1c87390a494
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:38:18.239822+00:00
-- url     : https://prove2.me/theorems/378d12e3-9906-4d62-aec3-e6c38cf06eec
-- title:
--   P2 M Ground Theory Heights  Heights Slice Lelong Error exists bound derivs a1c87390a494: P2 M Ground Theory Heights  Heights Slice Lelong Error exists bound derivs a1c87390a494
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Lelong Error exists bound derivs a1c87390a494 construction uses the P2 M Ground Theory Heights  Heights Slice Lelong Error exists bound derivs a1c87390a494 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLelongError.lean#L37-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLelongError.lean#L37-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLelongError
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceWeightBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBandEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceLelongError
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
open MvPolynomial Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.SliceLelongError

theorem P2M_GroundTheory_Heights__Heights_SliceLelongError_exists_bound_derivs_a1c87390a494 : ∃ M₁ M₂ : ℝ, (∀ s, |deriv Real.smoothTransition s| ≤ M₁) ∧
    ∀ s, |deriv (deriv Real.smoothTransition) s| ≤ M₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceLelongError».«exists_bound_derivs» := P2M_GroundTheory_Heights__Heights_SliceLelongError_exists_bound_derivs_a1c87390a494
