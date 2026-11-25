-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceLelongError_proof_a0b3c62d8b86
-- name    : P2M_GroundTheory_Heights__Heights_SliceLelongError_proof_a0b3c62d8b86
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:39:05.073052+00:00
-- url     : https://prove2.me/theorems/8bd2a7b1-c44f-40c9-b461-d713c7910081
-- title:
--   P2 M Ground Theory Heights  Heights Slice Lelong Error proof a0b3c62d8b86: P2 M Ground Theory Heights  Heights Slice Lelong Error proof a0b3c62d8b86
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Lelong Error proof a0b3c62d8b86 construction uses the P2 M Ground Theory Heights  Heights Slice Lelong Error proof a0b3c62d8b86 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLelongError.lean#L70-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLelongError.lean#L70-L99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLelongError
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceWeightBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBandEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceLelongError
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceSectionMass_proof_139e377538c6

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

theorem P2M_GroundTheory_Heights__Heights_SliceLelongError_proof_a0b3c62d8b86 (h₁ : SliceCutChain.Statement) (h₂ : SliceWeightBound.Statement)
    (h₃ : SliceBandEnergy.Statement) : SliceLelongError.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceLelongError».«proof» := P2M_GroundTheory_Heights__Heights_SliceLelongError_proof_a0b3c62d8b86
