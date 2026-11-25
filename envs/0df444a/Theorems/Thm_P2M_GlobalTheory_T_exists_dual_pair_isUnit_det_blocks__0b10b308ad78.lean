-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_dual_pair_isUnit_det_blocks__0b10b308ad78
-- name    : P2M_GlobalTheory_T_exists_dual_pair_isUnit_det_blocks__0b10b308ad78
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:06:24.946801+00:00
-- url     : https://prove2.me/theorems/56b3e27e-9668-59fe-adaa-71b5af86c934
-- title:
--   P2 M Global Theory T exists dual pair is Unit det blocks  0b10b308ad78: P2 M Global Theory T exists dual pair is Unit det blocks  0b10b308ad78
-- statement:
--   The P2 M Global Theory T exists dual pair is Unit det blocks  0b10b308ad78 construction uses the P2 M Global Theory T exists dual pair is Unit det blocks  0b10b308ad78 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsDualPairIsUnitDetBlocksStatement.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsDualPairIsUnitDetBlocksStatement.lean#L7-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsDualPairIsUnitDetBlocks
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsDualPairIsUnitDetBlocksStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_dual_pair_isUnit_det_blocks__0b10b308ad78 : ∀ {R : Type} [CommRing R] [IsLocalRing R], IsUnit (2 : R) → ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) R), IsUnit S.det →
    ∀ (G₁ G₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R), IsUnit G₁.det →
      G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) →
      ∃ X₁ X₂ : Matrix (Fin n) (Fin n) R, X₁ᵀ * S + S * X₂ = 0 ∧
        IsUnit (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ + G₁.toBlocks₂₁ + G₁.toBlocks₂₂ +
          X₁ * (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ - G₁.toBlocks₂₁ - G₁.toBlocks₂₂)).det ∧
        IsUnit (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ + G₂.toBlocks₂₁ + G₂.toBlocks₂₂ +
          X₂ * (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ - G₂.toBlocks₂₁ - G₂.toBlocks₂₂)).det := by sorry

alias «GlobalTheory».«T».«exists_dual_pair_isUnit_det_blocks'» := P2M_GlobalTheory_T_exists_dual_pair_isUnit_det_blocks__0b10b308ad78
