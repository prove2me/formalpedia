-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_exists_zsmul_mem_dualLattice_a99542587a2d
-- name    : P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_exists_zsmul_mem_dualLattice_a99542587a2d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:15.344912+00:00
-- url     : https://prove2.me/theorems/09c72176-89db-4c74-b432-6a5c78587358
-- title:
--   P2 M Ground Theory Heights  Heights Dual Embedding Bijective exists zsmul mem dual Lattice a99542587a2d: P2 M Ground Theory Heights  Heights Dual Embedding Bijective exists zsmul mem dual Lattice a995
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Embedding Bijective exists zsmul mem dual Lattice a99542587a2d construction uses the P2 M Ground Theory Heights  Heights Dual Embedding Bijective exists zsmul mem dual Lattice a99542587a2d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualEmbBijective.lean#L15-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualEmbBijective.lean#L15-L45

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

theorem P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_exists_zsmul_mem_dualLattice_a99542587a2d (F : HermLattice K i) (y : Fin i → K) :
    ∃ N : ℤ, N ≠ 0 ∧ N • y ∈ dualLattice F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualEmbeddingBijective».«exists_zsmul_mem_dualLattice» := P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_exists_zsmul_mem_dualLattice_a99542587a2d
