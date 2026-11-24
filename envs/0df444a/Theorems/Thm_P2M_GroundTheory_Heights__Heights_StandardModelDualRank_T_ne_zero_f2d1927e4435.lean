-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_T_ne_zero_f2d1927e4435
-- name    : P2M_GroundTheory_Heights__Heights_StandardModelDualRank_T_ne_zero_f2d1927e4435
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:41.369846+00:00
-- url     : https://prove2.me/theorems/6cea72bd-a382-430b-ac53-a35c15976aab
-- title:
--   P2 M Ground Theory Heights  Heights Standard Model Dual Rank T ne zero f2d1927e4435: P2 M Ground Theory Heights  Heights Standard Model Dual Rank T ne zero f2d1927e4435
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Model Dual Rank T ne zero f2d1927e4435 construction uses the P2 M Ground Theory Heights  Heights Standard Model Dual Rank T ne zero f2d1927e4435 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L134-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L134-L137

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

theorem P2M_GroundTheory_Heights__Heights_StandardModelDualRank_T_ne_zero_f2d1927e4435 : dualStdModelT K i ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardModelDualRank».«T_ne_zero» := P2M_GroundTheory_Heights__Heights_StandardModelDualRank_T_ne_zero_f2d1927e4435
