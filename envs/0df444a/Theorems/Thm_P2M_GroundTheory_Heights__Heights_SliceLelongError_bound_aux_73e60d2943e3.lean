-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceLelongError_bound_aux_73e60d2943e3
-- name    : P2M_GroundTheory_Heights__Heights_SliceLelongError_bound_aux_73e60d2943e3
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:38:32.973637+00:00
-- url     : https://prove2.me/theorems/c8726eb4-a0b6-4550-8e7a-3c1109ee21f9
-- title:
--   P2 M Ground Theory Heights  Heights Slice Lelong Error bound aux 73e60d2943e3: P2 M Ground Theory Heights  Heights Slice Lelong Error bound aux 73e60d2943e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Lelong Error bound aux 73e60d2943e3 construction uses the P2 M Ground Theory Heights  Heights Slice Lelong Error bound aux 73e60d2943e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLelongError.lean#L49-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLelongError.lean#L49-L68

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

theorem P2M_GroundTheory_Heights__Heights_SliceLelongError_bound_aux_73e60d2943e3 {P Q A B k : ℝ} (hk : 0 ≤ k) (hP : |P| ≤ A)
    (hQ : |Q| ≤ B * (2 * (k + 1) - (k + 1) + 1)) :
    |-(k + 1)⁻¹ * P + (k + 1)⁻¹ ^ 2 * Q| ≤ (|A| + 2 * |B|) / (k + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceLelongError».«bound_aux» := P2M_GroundTheory_Heights__Heights_SliceLelongError_bound_aux_73e60d2943e3
