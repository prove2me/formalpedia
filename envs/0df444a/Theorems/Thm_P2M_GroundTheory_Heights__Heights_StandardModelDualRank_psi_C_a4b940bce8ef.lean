-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_psi_C_a4b940bce8ef
-- name    : P2M_GroundTheory_Heights__Heights_StandardModelDualRank_psi_C_a4b940bce8ef
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:27.434407+00:00
-- url     : https://prove2.me/theorems/0c710f98-7b9d-488b-85cf-df00cffe6068
-- title:
--   P2 M Ground Theory Heights  Heights Standard Model Dual Rank psi C a4b940bce8ef: P2 M Ground Theory Heights  Heights Standard Model Dual Rank psi C a4b940bce8ef
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Model Dual Rank psi C a4b940bce8ef construction uses the P2 M Ground Theory Heights  Heights Standard Model Dual Rank psi C a4b940bce8ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L58-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L58-L59

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

theorem P2M_GroundTheory_Heights__Heights_StandardModelDualRank_psi_C_a4b940bce8ef (k : K) : psi K i (C k) = embK K i k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardModelDualRank».«psi_C» := P2M_GroundTheory_Heights__Heights_StandardModelDualRank_psi_C_a4b940bce8ef
