-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_w_eq_4239f43f32aa
-- name    : P2M_GroundTheory_Heights__Heights_StandardModelDualRank_w_eq_4239f43f32aa
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:57.999946+00:00
-- url     : https://prove2.me/theorems/66431e5a-1c2c-4ff7-a497-76371dafa18a
-- title:
--   P2 M Ground Theory Heights  Heights Standard Model Dual Rank w eq 4239f43f32aa: P2 M Ground Theory Heights  Heights Standard Model Dual Rank w eq 4239f43f32aa
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Model Dual Rank w eq 4239f43f32aa construction uses the P2 M Ground Theory Heights  Heights Standard Model Dual Rank w eq 4239f43f32aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L147-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L147-L151

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

theorem P2M_GroundTheory_Heights__Heights_StandardModelDualRank_w_eq_4239f43f32aa (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (t : T) :
    w b t = ∑ j, embK K i ((b t : Fin i → K) j) * u K i j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardModelDualRank».«w_eq» := P2M_GroundTheory_Heights__Heights_StandardModelDualRank_w_eq_4239f43f32aa
