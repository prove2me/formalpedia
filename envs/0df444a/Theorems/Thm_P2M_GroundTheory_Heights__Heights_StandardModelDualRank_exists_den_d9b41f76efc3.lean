-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_exists_den_d9b41f76efc3
-- name    : P2M_GroundTheory_Heights__Heights_StandardModelDualRank_exists_den_d9b41f76efc3
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:40:20.079735+00:00
-- url     : https://prove2.me/theorems/916bcaa0-0fe7-4bd4-ad0c-26f3f1f85d1b
-- title:
--   P2 M Ground Theory Heights  Heights Standard Model Dual Rank exists den d9b41f76efc3: P2 M Ground Theory Heights  Heights Standard Model Dual Rank exists den d9b41f76efc3
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Model Dual Rank exists den d9b41f76efc3 construction uses the P2 M Ground Theory Heights  Heights Standard Model Dual Rank exists den d9b41f76efc3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L64-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L64-L71

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

theorem P2M_GroundTheory_Heights__Heights_StandardModelDualRank_exists_den_d9b41f76efc3 {f : dualStdModelField K i} (hf : f ∈ Subfield.closure (Set.range (u K i))) :
    ∃ d ∈ (psiZ K i).range, d ≠ 0 ∧ d * f ∈ (psiZ K i).range := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardModelDualRank».«exists_den» := P2M_GroundTheory_Heights__Heights_StandardModelDualRank_exists_den_d9b41f76efc3
