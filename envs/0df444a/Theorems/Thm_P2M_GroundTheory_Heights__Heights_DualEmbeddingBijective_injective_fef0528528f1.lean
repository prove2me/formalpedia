-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_injective_fef0528528f1
-- name    : P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_injective_fef0528528f1
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:20.645898+00:00
-- url     : https://prove2.me/theorems/3c3a8857-9980-4df5-94c2-e88c994f9ecd
-- title:
--   P2 M Ground Theory Heights  Heights Dual Embedding Bijective injective fef0528528f1: P2 M Ground Theory Heights  Heights Dual Embedding Bijective injective fef0528528f1
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Embedding Bijective injective fef0528528f1 construction uses the P2 M Ground Theory Heights  Heights Dual Embedding Bijective injective fef0528528f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualEmbBijective.lean#L63-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualEmbBijective.lean#L63-L91

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

theorem P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_injective_fef0528528f1 (F : HermLattice K i) {T : Type} [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice F)) :
    Function.Injective (Matrix.mulVecLin (dualEmbMatrix b)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualEmbeddingBijective».«injective» := P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_injective_fef0528528f1
