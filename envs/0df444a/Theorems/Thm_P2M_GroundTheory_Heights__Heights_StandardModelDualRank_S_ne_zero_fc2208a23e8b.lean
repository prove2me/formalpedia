-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_S_ne_zero_fc2208a23e8b
-- name    : P2M_GroundTheory_Heights__Heights_StandardModelDualRank_S_ne_zero_fc2208a23e8b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:46.970133+00:00
-- url     : https://prove2.me/theorems/8e116ed7-6621-4703-ac9c-42e4dd901938
-- title:
--   P2 M Ground Theory Heights  Heights Standard Model Dual Rank S ne zero fc2208a23e8b: P2 M Ground Theory Heights  Heights Standard Model Dual Rank S ne zero fc2208a23e8b
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Model Dual Rank S ne zero fc2208a23e8b construction uses the P2 M Ground Theory Heights  Heights Standard Model Dual Rank S ne zero fc2208a23e8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L128-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L128-L131

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
variable [NumberField K]
variable {T : Type}
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_StandardModelDualRank_S_ne_zero_fc2208a23e8b : dualStdModelS K i ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardModelDualRank».«S_ne_zero» := P2M_GroundTheory_Heights__Heights_StandardModelDualRank_S_ne_zero_fc2208a23e8b
