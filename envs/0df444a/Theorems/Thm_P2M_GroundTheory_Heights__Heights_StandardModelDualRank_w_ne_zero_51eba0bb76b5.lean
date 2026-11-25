-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_w_ne_zero_51eba0bb76b5
-- name    : P2M_GroundTheory_Heights__Heights_StandardModelDualRank_w_ne_zero_51eba0bb76b5
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:42:49.095812+00:00
-- url     : https://prove2.me/theorems/6aa507c9-a4c3-57af-aba0-33aa5b88fa90
-- title:
--   P2 M Ground Theory Heights  Heights Standard Model Dual Rank w ne zero 51eba0bb76b5: P2 M Ground Theory Heights  Heights Standard Model Dual Rank w ne zero 51eba0bb76b5
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Model Dual Rank w ne zero 51eba0bb76b5 construction uses the P2 M Ground Theory Heights  Heights Standard Model Dual Rank w ne zero 51eba0bb76b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L144-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L144-L145

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

theorem P2M_GroundTheory_Heights__Heights_StandardModelDualRank_w_ne_zero_51eba0bb76b5 (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (t : T) : w b t ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardModelDualRank».«w_ne_zero» := P2M_GroundTheory_Heights__Heights_StandardModelDualRank_w_ne_zero_51eba0bb76b5
