-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_psi_X_d961fe179bbd
-- name    : P2M_GroundTheory_Heights__Heights_StandardModelDualRank_psi_X_d961fe179bbd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:46.10483+00:00
-- url     : https://prove2.me/theorems/64308313-dfb2-4129-b9ac-e4e08c5f99bd
-- title:
--   P2 M Ground Theory Heights  Heights Standard Model Dual Rank psi X d961fe179bbd: P2 M Ground Theory Heights  Heights Standard Model Dual Rank psi X d961fe179bbd
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Model Dual Rank psi X d961fe179bbd construction uses the P2 M Ground Theory Heights  Heights Standard Model Dual Rank psi X d961fe179bbd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L55-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L55-L56

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

theorem P2M_GroundTheory_Heights__Heights_StandardModelDualRank_psi_X_d961fe179bbd (j : Fin i) : psi K i (X j) = u K i j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardModelDualRank».«psi_X» := P2M_GroundTheory_Heights__Heights_StandardModelDualRank_psi_X_d961fe179bbd
