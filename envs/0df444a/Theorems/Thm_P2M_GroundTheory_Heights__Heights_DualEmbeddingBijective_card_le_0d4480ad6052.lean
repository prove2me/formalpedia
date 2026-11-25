-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_card_le_0d4480ad6052
-- name    : P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_card_le_0d4480ad6052
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:26.389524+00:00
-- url     : https://prove2.me/theorems/4eeb2812-ec34-40d4-b2a8-a64f5e705aad
-- title:
--   P2 M Ground Theory Heights  Heights Dual Embedding Bijective card le 0d4480ad6052: P2 M Ground Theory Heights  Heights Dual Embedding Bijective card le 0d4480ad6052
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Embedding Bijective card le 0d4480ad6052 construction uses the P2 M Ground Theory Heights  Heights Dual Embedding Bijective card le 0d4480ad6052 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualEmbBijective.lean#L93-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualEmbBijective.lean#L93-L105

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualEmbBijective
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
open NumberField Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.DualEmbeddingBijective
variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_card_le_0d4480ad6052 (F : HermLattice K i) {T : Type} [Fintype T]
    (b : Module.Basis T ℤ (dualLattice F)) :
    Fintype.card T ≤ Fintype.card ((K →+* ℂ) × Fin i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualEmbeddingBijective».«card_le» := P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_card_le_0d4480ad6052
