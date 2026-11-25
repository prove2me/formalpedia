-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_exists_int_smul_mem_4c8901af79bb
-- name    : P2M_GroundTheory_Heights__Heights_StandardModelDualRank_exists_int_smul_mem_4c8901af79bb
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:30.602546+00:00
-- url     : https://prove2.me/theorems/daa7492a-372f-4df8-b0ff-06ecd7c0c453
-- title:
--   P2 M Ground Theory Heights  Heights Standard Model Dual Rank exists int smul mem 4c8901af79bb: P2 M Ground Theory Heights  Heights Standard Model Dual Rank exists int smul mem 4c8901af79bb
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Model Dual Rank exists int smul mem 4c8901af79bb construction uses the P2 M Ground Theory Heights  Heights Standard Model Dual Rank exists int smul mem 4c8901af79bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L99-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L99-L120

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

theorem P2M_GroundTheory_Heights__Heights_StandardModelDualRank_exists_int_smul_mem_4c8901af79bb (F : HermLattice K i) (v : Fin i → K) :
    ∃ N : ℤ, N ≠ 0 ∧ (N : K) • v ∈ dualLattice F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardModelDualRank».«exists_int_smul_mem» := P2M_GroundTheory_Heights__Heights_StandardModelDualRank_exists_int_smul_mem_4c8901af79bb
