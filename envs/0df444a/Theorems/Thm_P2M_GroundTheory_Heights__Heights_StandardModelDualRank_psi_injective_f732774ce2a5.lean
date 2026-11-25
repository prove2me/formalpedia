-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_psi_injective_f732774ce2a5
-- name    : P2M_GroundTheory_Heights__Heights_StandardModelDualRank_psi_injective_f732774ce2a5
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:36.454572+00:00
-- url     : https://prove2.me/theorems/6a6d58db-17ca-4a6c-a00c-f26db851bf43
-- title:
--   P2 M Ground Theory Heights  Heights Standard Model Dual Rank psi injective f732774ce2a5: P2 M Ground Theory Heights  Heights Standard Model Dual Rank psi injective f732774ce2a5
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Model Dual Rank psi injective f732774ce2a5 construction uses the P2 M Ground Theory Heights  Heights Standard Model Dual Rank psi injective f732774ce2a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L50-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardModelDualRank
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField DualArithmeticVariety
noncomputable section
open GroundTheory.Heights₂.Heights.StandardModelDualRank
variable {K : Type} [Field K] {i : ℕ}

theorem P2M_GroundTheory_Heights__Heights_StandardModelDualRank_psi_injective_f732774ce2a5 : Function.Injective (psi K i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardModelDualRank».«psi_injective» := P2M_GroundTheory_Heights__Heights_StandardModelDualRank_psi_injective_f732774ce2a5
