-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DiffStepExpansion_single_mem_981521d3974d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_DiffStepExpansion_single_mem_981521d3974d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:47.060787+00:00
-- url     : https://prove2.me/theorems/07140b28-bfc7-42d6-83d8-9bd6665d539d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Diff Step Expansion single mem 981521d3974d: P2 M Ground Theory Heights  Heights Numbers DVR Diff Step Expansion single mem 981521d3974d
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Diff Step Expansion single mem 981521d3974d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Diff Step Expansion single mem 981521d3974d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDiffStepExpansion.lean#L81-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDiffStepExpansion.lean#L81-L82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDiffStepExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.DiffStepExpansion
variable {K : Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_DiffStepExpansion_single_mem_981521d3974d [DecidableEq K] (k : K) : (Pi.single k 1 : K → ℤ) ∈ expandable K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«DiffStepExpansion».«single_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_DiffStepExpansion_single_mem_981521d3974d
