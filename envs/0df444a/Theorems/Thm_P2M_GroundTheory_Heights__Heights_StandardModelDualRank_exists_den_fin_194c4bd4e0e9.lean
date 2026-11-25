-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_exists_den_fin_194c4bd4e0e9
-- name    : P2M_GroundTheory_Heights__Heights_StandardModelDualRank_exists_den_fin_194c4bd4e0e9
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:27.99762+00:00
-- url     : https://prove2.me/theorems/ab4cfa07-1bb8-4080-9a99-1bcc1b2ef899
-- title:
--   P2 M Ground Theory Heights  Heights Standard Model Dual Rank exists den fin 194c4bd4e0e9: P2 M Ground Theory Heights  Heights Standard Model Dual Rank exists den fin 194c4bd4e0e9
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Model Dual Rank exists den fin 194c4bd4e0e9 construction uses the P2 M Ground Theory Heights  Heights Standard Model Dual Rank exists den fin 194c4bd4e0e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L73-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L73-L80

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

theorem P2M_GroundTheory_Heights__Heights_StandardModelDualRank_exists_den_fin_194c4bd4e0e9 {n : ℕ} (f : Fin n → dualStdModelField K i)
    (hf : ∀ k, f k ∈ Subfield.closure (Set.range (u K i))) :
    ∃ D ∈ (psiZ K i).range, D ≠ 0 ∧ ∀ k, D * f k ∈ (psiZ K i).range := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardModelDualRank».«exists_den_fin» := P2M_GroundTheory_Heights__Heights_StandardModelDualRank_exists_den_fin_194c4bd4e0e9
